# The Ril Language Specification

**Version:** 0.1.0  
**Status:** Canonical Reference Specification  
**Format:** Code-First Normative Document  

---


## Document Conventions

- **Normative Invariants**: Language guarantees and type safety rules are formally declared under titled normative invariants. All conforming Ril implementations must enforce these invariants unconditionally.
- **Grammar Productions**: Syntactic grammar is formally specified in Extended Backus-Naur Form (EBNF).
- **Normative Code Annotations**: Code examples define normative verification cases in the stated fixture context:
  - `-- OK`: Syntactically and semantically valid Ril programs.
  - `-- Error [EXXXX]`: Programs that must be statically rejected by the compiler with the indicated diagnostic error code.
  - `-- Panics`: Programs that raise deterministic runtime panics under defect conditions.
- **Examples**: Blocks are independent fixtures unless marked as complete source files.
- Local statements run in an enclosing callable; displayed declarations belong to its enclosing declaration scope. Free names are typed fixture inputs or supplied contracts.
- Fixtures handle their local expressions' effects. Named functions and complete files obey their own annotations, casing, and initialization rules.
- Negative statements are checked individually with valid setup. Blocks containing `...` are schematic.
- Static-evaluation fixtures use the selected abstract target and a sufficient evaluation budget unless a budget-exhaustion case is explicitly specified.
- **Semantic Cross-References**: Internal specifications and rule cross-references link directly to their defining sections via Markdown anchors.
---

## Table of Contents

- [Notation, Abstract Machine, and Conformance](#notation-abstract-machine-and-conformance)
  - [Grammar Notation](#grammar-notation)
  - [Program Conformance](#program-conformance)
  - [Abstract Machine and Memory Semantics](#abstract-machine-and-memory-semantics)
  - [Failure Model and Error Categories](#failure-model-and-error-categories)
- [Source Text and Lexical Elements](#source-text-and-lexical-elements)
  - [Character Set and Encoding](#character-set-and-encoding)
  - [Comments](#comments)
  - [Whitespace and Layout Rules](#whitespace-and-layout-rules)
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
  - [Nominal Type Wrappers](#nominal-type-wrappers)
  - [Deep Immutability](#deep-immutability)
  - [Type Identity and Subtyping](#type-identity-and-subtyping)
  - [Memory Model and Handle Invariants](#memory-model-and-handle-invariants)
  - [Complete Provenance and Optional Annotations](#complete-provenance-and-optional-annotations)
  - [Functional Updates via Derive](#functional-updates-via-derive)
  - [Generic Parameters, Defaults, and Value Sorts](#generic-parameters-defaults-and-value-sorts)
  - [Tripartite Ontology and Type Definition Boundaries](#tripartite-ontology-and-type-definition-boundaries)
- [Declarations and Bindings](#declarations-and-bindings)
  - [Binding Permissions and Storage Matrix](#binding-permissions-and-storage-matrix)
  - [Immutable Bindings](#immutable-bindings)
  - [Pinned Mutable Handles](#pinned-mutable-handles)
  - [Reassignable Mutable Variables](#reassignable-mutable-variables)
  - [Scoped Resource Bindings](#scoped-resource-bindings)
  - [Live View Bindings](#live-view-bindings)
  - [Type Declarations and Opaque Types](#type-declarations-and-opaque-types)
  - [Effect Declarations](#effect-declarations)
  - [External Interface Declarations](#external-interface-declarations)
- [Expressions and Operators](#expressions-and-operators)
  - [Operator Precedence and Associativity](#operator-precedence-and-associativity)
  - [Arithmetic and Wrapping Operators](#arithmetic-and-wrapping-operators)
  - [Bitwise and Shift Operators](#bitwise-and-shift-operators)
  - [Relational, Equality, and Containment Operators](#relational-equality-and-containment-operators)
  - [Logical Operators](#logical-operators)
  - [Range and Slicing Expressions](#range-and-slicing-expressions)
  - [Pipeline Operators](#pipeline-operators)
  - [Error and Fallback Operators](#error-and-fallback-operators)
  - [Record Construction and Functional Update](#record-construction-and-functional-update)
  - [Assignments and Compound Assignments](#assignments-and-compound-assignments)
- [Control Flow and Pattern Matching](#control-flow-and-pattern-matching)
  - [Block Expressions, Tail Values, and Hoisted Declarations](#block-expressions-tail-values-and-hoisted-declarations)
  - [Conditional Expressions](#conditional-expressions)
  - [Loop Expressions](#loop-expressions)
  - [Control Transfers](#control-transfers)
  - [Guarded Bindings and Non-Vacuous Invariant](#guarded-bindings-and-non-vacuous-invariant)
  - [Pattern Matching](#pattern-matching)
  - [Pattern Syntax, Or-Patterns, and Exhaustiveness](#pattern-syntax-or-patterns-and-exhaustiveness)
  - [Flow-Sensitive Type Narrowing](#flow-sensitive-type-narrowing)
- [Functions, Closures, and Callables](#functions-closures-and-callables)
  - [Named Function Declarations and Contrast Matrix](#named-function-declarations-and-contrast-matrix)
  - [Default Purity and Callback Dependencies](#default-purity-and-callback-dependencies)
  - [Parameter Modes, Caller Obligations, and Defaults](#parameter-modes-caller-obligations-and-defaults)
  - [Anonymous Functions, Trailing Closures, and Projection Accessors](#anonymous-functions-trailing-closures-and-projection-accessors)
  - [Closures, Factory Signatures, and Lexical Environments](#closures-factory-signatures-and-lexical-environments)
  - [Higher-Order Functions and Capability Forwarding](#higher-order-functions-and-capability-forwarding)
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
  - [Callable Signature Abstraction](#callable-signature-abstraction)
- [Algebraic Effects and Concurrency](#algebraic-effects-and-concurrency)
  - [Effect Declarations and Operation Signatures](#effect-declarations-and-operation-signatures)
  - [Effect Handlers](#effect-handlers)
  - [Affine Resumption and Delimited Early Abort](#affine-resumption-and-delimited-early-abort)
  - [Built-in System Effects](#built-in-system-effects)
  - [Structured Concurrency and Panic Containment](#structured-concurrency-and-panic-containment)
  - [Deterministic Data Parallelism and Divide-and-Conquer Primitives](#deterministic-data-parallelism-and-divide-and-conquer-primitives)
  - [Structured Concurrency Channels](#structured-concurrency-channels)
  - [Arrow-Only Law of Effects](#arrow-only-law-of-effects)
- [Compile-Time Computation and Totality](#compile-time-computation-and-totality)
  - [Static Type Values and Type Quotation](#static-type-values-and-type-quotation)
  - [Pure Type Functions and Type Return Privilege](#pure-type-functions-and-type-return-privilege)
  - [Disjoint Call Families, Evaluation Budgets, and Branch Pruning](#disjoint-call-families-evaluation-budgets-and-branch-pruning)
  - [Unified Tripartite Introspection](#unified-tripartite-introspection)
    - [Static Key Parameters and Computed Value Projection](#static-key-parameters-and-computed-value-projection)
  - [Structural Type Pattern Matching](#structural-type-pattern-matching)
  - [Static Parameter Sorts and Adaptation Rules](#static-parameter-sorts-and-adaptation-rules)
  - [Compile-Time Execution and Layout Cooperation](#compile-time-execution-and-layout-cooperation)
- [Modules, Program Execution, and Prelude](#modules-program-execution-and-prelude)
  - [Modules and Compilation Units](#modules-and-compilation-units)
  - [Module Imports and Visibility](#module-imports-and-visibility)
  - [Top-Level Initialization and Purity](#top-level-initialization-and-purity)
  - [Test Conventions and Execution Protocol](#test-conventions-and-execution-protocol)
  - [Program Entry Point](#program-entry-point)
  - [Standard Prelude Built-ins](#standard-prelude-built-ins)
  - [Mandatory Inspection of Fallible Results](#mandatory-inspection-of-fallible-results)
- [Diagnostic Error Codes Summary](#diagnostic-error-codes-summary)

---

## Notation, Abstract Machine, and Conformance

### Grammar Notation

Grammar productions are specified in Extended Backus-Naur Form (EBNF):

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
let y: str = 42                        -- Error [E0301]: TypeMismatchError: expected type 'str', found 'int'
let z = 10 / 0                         -- Panics: division by zero
```

### Program Conformance

A conforming Ril implementation MUST:
- Accept all syntactically and semantically valid Ril programs defined herein.
- Statically reject all invalid programs with the exact diagnostic conditions specified herein.
- Emit artifacts adhering strictly to the abstract machine semantics, memory model, and determinism invariants.
- Enforce the complete provenance obligations below regardless of which optional annotations or diagnostic explanations are displayed. Static validity is determined by the specified conservative judgments, not by an assumption that arbitrary run-time behavior can be decided exactly.

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

Ril enforces a strict separation between domain recoverable errors and program defects:

- **Recoverable Errors**: Represented as ordinary sum type values (`Result<T, E>` and `Option<T>` / `?T`). Unused `Result` values are statically rejected.
- **Defects (Panics)**: Invariant violations (division by zero, out-of-bounds indexing, failed `assert`, integer overflow) raise **Deterministic Runtime Panics**.
- **Synchronous Isolation**: Panics cannot be caught within synchronous evaluation frames.
- **Boundary Containment**: In concurrent execution, child task panics are isolated at structured concurrency boundaries (`scope`), resolving to `Result<T, TaskFault>` (`TaskFault::Panicked`).

```ril
-- Recoverable error handling via Result and '?':
fn parse_id(s: str) -> Result<int, str> {
    if s == "" { Err("empty input") } else { Ok(42) }
}

fn init_session() -> Result<int, str> {
    let id = parse_id("10")?           -- OK: propagated via postfix '?' within function frame
    Ok(id)
}
-- let top_id = parse_id("10")?        -- Error [E0205]: QuestionMarkOutsideFunctionError: postfix '?' operator used outside function or closure body; no enclosing activation frame to receive early return
-- parse_id("10")                       -- Error [E0720]: UnusedFallibleResultError: unused fallible Result must be handled via '?', 'match', or fallback '??'

-- Deterministic runtime panic on defect:
let arr = [1, 2, 3]
let item = arr[5]                      -- Panics: index out of bounds (index 5, length 3)
let safe_item = arr?[5]                -- OK: safe index evaluates to Option<int> (None)

-- Synchronous Isolation: panics cannot be caught synchronously
fn faulty_frame() -> int {
    let _ = 10 / 0                     -- Panics: division by zero; aborts current stack frame immediately
    100                                -- Unreachable
}

-- Boundary Containment: child panics isolated at structured scope boundary
use ril/concurrent::{scope, TaskFault}

let scope_outcome: Result<int, TaskFault> = scope(\mut s -> {
    s.fork(\-> { panic("worker failure") })
    Ok(42)
})
-- scope_outcome evaluates to Err(TaskFault::Panicked(...))
assert(scope_outcome is Err(TaskFault::Panicked(_)))
```

---

## Source Text and Lexical Elements

### Character Set and Encoding

Source text is encoded in UTF-8. Case is significant.

### Comments

```ebnf
LineComment  ::= "--" { SourceChar } ( Newline | EOF )
BlockComment ::= "{-" { SourceChar | BlockComment } "-}"
```

```ril
-- Single-line comment to end of line
{- Block comment {- nested block comment -} continues -}
```

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

### Identifiers and Casing Invariants

```ebnf
Identifier         ::= PascalCase | SnakeCase | ScreamingSnakeCase | SuppressedVar
PascalCase         ::= [A-Z] { [a-zA-Z0-9] }
SnakeCase          ::= [a-z] [a-z0-9]* { "_" [a-z0-9]+ }
ScreamingSnakeCase ::= [A-Z] [A-Z0-9]* { "_" [A-Z0-9]+ }
SuppressedVar      ::= "_" [a-z] [a-z0-9]* { "_" [a-z0-9]+ }
Wildcard           ::= "_"
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
-- let ambiguous: First = Shared      -- Error [E0203]: expected type does not resolve the abbreviation
type Maybe<T> = Option<T>
let value: Maybe<int> = Some(1)        -- OK: an alias adds no constructor candidate
```

Declarations and imports share one namespace. Same-scope duplicates are `E0203`; inner declarations may shadow outer ones, including the enclosing prelude.

| Name | Resolution |
| :--- | :--- |
| Nominal type/constructor; predefined `Set<T>`/`Set::from` | Roles of one declaration; separate user declarations cannot merge |
| `S::V` | Variant member of S; no second enclosing-scope declaration |
| Unqualified constructor name | Ordinary lexical binding first; otherwise require one variant candidate (`E0203` if ambiguous) |
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
-- type user_doc = { id: int }         -- Error [E0101]: InvalidIdentifierCasingError: type identifier must be PascalCase, found 'user_doc'
-- fn Calculate() -> () {}             -- Error [E0101]: InvalidIdentifierCasingError: function identifier must be snake_case, found 'Calculate'
-- let UserCount = 10                  -- Error [E0101]: InvalidIdentifierCasingError: variable identifier must be snake_case, found 'UserCount'
-- meta let max_size = 100             -- Error [E0101]: InvalidIdentifierCasingError: compile-time constant must be SCREAMING_SNAKE_CASE, found 'max_size'
-- var ACTIVE_FLAG = true              -- Error [E0101]: InvalidIdentifierCasingError: top-level mutable variable must be snake_case, found 'ACTIVE_FLAG'
-- type HTTPServer = { port: int }     -- Error [E0102]: MalformedIdentifierSyntaxError: acronym in PascalCase must be title-cased, expected 'HttpServer', found 'HTTPServer'
-- let user__name = "Alice"            -- Error [E0102]: MalformedIdentifierSyntaxError: consecutive underscores are prohibited, found 'user__name'
-- let Some(USER_ID) = opt             -- Error [E0103]: PatternCasingCollisionError: pattern binding position cannot use uppercase identifier 'USER_ID'
-- let _ = 10; println(_)              -- Error [E0322]: WildcardExpressionError: wildcard '_' cannot be evaluated as an expression
```

### Keywords

The following 34 tokens are strictly reserved keywords; they cannot be ordinary identifiers or field labels:

```
as       eff      else     false    fn
for      halt     if       in       is
keyof    last     let      loop     match
meta     module   mut      never    next
opaque   pub      resume   return   scoped
true     type     typeof   use      var
view     where    while    with
```

`closure` remains an ordinary identifier. In a state group, a leading `closure` followed by a comma, or by a capture-owner name and a comma, is a contextual group header. This interpretation is fixed before name resolution; it never falls back to a list of global names. The state-group rules specify the remaining cases.

```ril
-- Reserved keywords in action:
pub opaque type Token = int            -- 'pub', 'opaque', 'type'
meta let COMPILE_ID = 101              -- 'meta', 'let'
eff Logger { log(str) -> () }          -- 'eff'
use ril/array::{push}                  -- 'use'
halt fn total_step() -> bool { true }  -- 'halt', 'true', 'fn'
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
```

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
-- let too_large: i8 = 128i8            -- Error [E0301]: literal is outside its selected type's range
-- let mixed = 1u8 + 1u16               -- Error [E0301]: no implicit numeric promotion
```

| Form | Type / check |
| :--- | :--- |
| Suffixed literal | Suffix fixes the type |
| Unsuffixed integer | Compatible numeric context, otherwise `int`; round once if selected as floating-point |
| Unsuffixed float | Contextual `f32`/`f64`, otherwise `f64` |
| Integer-typed literal | Must fit its type (`E0301`); an immediately applied `-` is included in the range check |
| Negating an evaluated fixed-width minimum | Panic; the literal exception does not apply |
| Numeric arithmetic/comparison | Same operand type (`E0301`); no conversion of already typed values |
| Shift count | Integer; need not have the left operand's width |
| Fixed array length | Static nonnegative `int`; wrong sort/negative: `E0323`, run-time value: `E0810` |

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


- Strings contain Unicode scalars. Escapes: `\n`, `\r`, `\t`, `\0`, `\\`, `\"`, `\u{hex_digits}`. Invalid scalars/escapes are `E0102`.
- Interpolated strings use `{{` and `}}` for literal braces.
- Raw strings have no escapes/interpolation and cannot contain their closing backtick.
- Byte literals contain ASCII or `\xHH` with exactly two hex digits.

Combine strings and values with interpolation, such as `"Hello, {name}"`. Arithmetic operators do not perform string conversion or concatenation.

A leading zero in a numeric format width, as in `04x`, selects zero padding. Otherwise the default fill is a space. Width counts Unicode scalars; precision for `f` is digits after the decimal point. A format specifier incompatible with the value type is `E0301`.

### Boolean and Unit Literals

```ril
let is_valid = true                    -- Type: bool
let is_done = false                    -- Type: bool
let unit_val = ()                      -- Type: ()
```

---

## Types and Memory Model

### Value Types

Value types have copy-by-value semantics. They cannot be borrowed as `mut` parameters.

| Category | Types | Default Alignment / Size |
| :--- | :--- | :--- |
| Boolean | `bool` | 1 byte |
| Signed Integers | `i8`, `i16`, `i32`, `i64`, `int` (pointer-sized) | 1, 2, 4, 8, pointer bytes |
| Unsigned Integers | `u8`, `u16`, `u32`, `u64` | 1, 2, 4, 8 bytes |
| Arbitrary Precision | `bigint` | Managed heap integer |
| Floating-Point | `f32`, `f64` | 4, 8 bytes (IEEE 754) |
| Text & Data | `str` (UTF-8 immutable), `bytes` (byte slice) | Pointer + length |
| Unit & Bottom | `()` (unit, 1 value), `never` (empty, diverges) | 0 bytes |

```ril
-- Value types: independent copy-by-value semantics:
let a: int = 42
var b = a                              -- Independent copy; value types use 'var' for mutation
b += 1                                 -- Modifies 'b'; 'a' remains 42
assert(a == 42 && b == 43)

-- let mut bad_scalar = a              -- Error [E0402]: ValueTypePinnedMutError: value type 'int' has no interior mutability; use 'var'
-- fn bad_borrow(mut x: int) {}        -- Error [E0401]: ValueTypeMutableBorrowError: value type 'int' cannot be borrowed as 'mut' parameter
```

### Reference Types

Reference types are allocated on the managed garbage-collected heap: records, arrays, tuples, maps, sets, and sum type instances.

```ril
-- Reference types: shared heap aliasing:
type Node = { mut val: int }
let mut n1 = Node.{ val: 10 }
let view n2 = n1                       -- 'n2' aliases the exact same heap record as a live view
n1.val = 99                            -- Mutate through 'n1'
assert(n2.val == 99)                   -- OK: 'n2' observes mutation due to reference aliasing

-- Mutating through read-only alias is strictly prohibited:
-- n2.val = 100                        -- Error [E0520]: MutabilityLaunderingError: cannot mutate field 'val' through read-only view 'n2'
```

### Record Types and Row Polymorphism

- Field `mut` permits replacing that slot. A projected reference retains its stored origin and permissions, limited by the permissions of the entire access path. Slot mutability neither upgrades a child reference nor makes its data immutable.
- Named rows contain the fields not explicitly declared. Overlapping labels are `E0302`.

Records have structural named fields. Closed records reject width subtyping; open records use declared or structurally bound `..R`, never anonymous `..`.

Use `r.field` or a statically known `r.(key)`. Types use the corresponding `T.field`/`T.(key)`. Record bracket indexing and run-time keys are `E0324`.

Named row tail polymorphism (`..R`) allows generic functions to accept and preserve additional caller fields across pipelines. Pattern destructuring with `..rest` extracts a concrete, statically typed sub-record containing the remaining known fields.

```ebnf
RecordType       ::= "{" [ RecordFieldList ] "}"
RecordField      ::= [ "mut" ] FieldLabel ":" TypeExpression
TypeProjection ::= PrimaryType "." ( Identifier | TupleIndex | "(" Expression ")" )
TupleIndex     ::= Digit { Digit }
```

```ril
type User = { id: int, name: str }
let u: User = .{ id: 1, name: "Alice" } -- OK: exact closed record match

-- Closed record rejects unexpected fields (E0302):
-- let bad_u: User = .{ id: 1, name: "Alice", age: 30 } -- Error [E0302]: UnexpectedFieldError: unexpected field 'age' in closed record 'User'

-- Field access is strictly compile-time identifier dot-access:
let user_id = u.id                     -- OK: static field projection
-- let bad_index = u["name"]           -- Error [E0324]: DynamicRecordIndexProhibitedError: records do not support dynamic index lookup
let static_accessor = u.("name")       -- OK: a statically known key, not a dynamic lookup

-- Type-level field projection:
type IdType = User.id                  -- OK: direct static field type extraction (int)
-- type BadIndex = User["id"]          -- Error [E0324]: DynamicRecordIndexProhibitedError: record types do not support bracket indexing, use User.id

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

Bracket syntax (`[...]`) unifies linear sequences (dynamic slices `[]T` and compile-time fixed-length arrays `[N]T`) and associative maps (`[K: V]`). Fixed-arity anonymous products are represented as tuples (`(T1, T2)`). The unique set type `Set<T>` is provided as a standard library collection type via the prelude `Set` module, rather than dedicated core language syntax.

```ebnf
ArrayType   ::= "[" [ Expression ] "]" TypeExpression
MapType     ::= "[" TypeExpression ":" TypeExpression "]"
TupleType        ::= "(" TypeExpression "," TypeExpression { "," TypeExpression } [ "," ] ")"
```

```ril
-- Linear Array ([]T dynamic slice, [N]T fixed-length array):
let numbers: []int = [1, 2, 3]         -- Type: []int (dynamic slice)
let buffer: [4]u8 = [0, 0, 0, 0]       -- Type: [4]u8 (fixed-length array)

-- Associative Map ([K: V]):
let config: [str: str] = ["env": "prod", "host": "127.0.0.1"]
let empty_map: [str: int] = [:]        -- Empty map literal
let host = config["host"]              -- Evaluates to ?str (Some("127.0.0.1"))

-- Prelude Unique Set (Set<T>):
let visited: Set<int> = Set::from([10, 20, 30]) -- Constructed via prelude Set module
let roles = Set::of(["admin", "guest"])

-- Tuple ((T1, T2)):
let coords: (int, str) = (10, "Alice") -- Type: (int, str)
let x = coords.0                       -- Value positional access: 10
let name = coords.1                    -- Value positional access: "Alice"
type CoordX = (typeof coords).0        -- Inferred tuple positional projection: int
type First = (int, str).0              -- Static tuple positional projection: int
-- type OutOfBounds = (int, str).2      -- Error [E0312]: TupleIndexOutOfBoundsError: tuple index 2 out of bounds for (int, str)

-- Collection Type Parameter Extraction (modular, non-prelude):
use ril/array::{Elem}
use ril/map::{Key, Value}

type IntElem = Elem<[]int>             -- Resolves to int
type HostKey = Key<[str: int]>         -- Resolves to str
type PortVal = Value<[str: int]>       -- Resolves to int

-- Collections are not product types; dot projection on collections is rejected:
-- type BadArrElem = ([]int).elem      -- Error [E0301]: TypeMismatchError: collection type '[]int' has no named fields or member projections; use 'ril/array::{Elem}'
-- type BadMapKey = ([str: int]).key   -- Error [E0301]: TypeMismatchError: collection type '[str: int]' has no named fields or member projections; use 'ril/map::{Key}'
```

### Sum Types and GADTs

Sum types represent tagged disjoint unions. Constructor equations allow generalized algebraic data types (GADTs).

```ebnf
SumTypeDecl         ::= [ "pub" ] "type" Identifier [ GenericParams ] [ WhereClause ]
                        "{" VariantDecl { "," VariantDecl } [ "," ] "}"
VariantDecl      ::= PascalCase [ GenericParams ] [ VariantPayload ] [ "->" TypeExpression ]
VariantFields       ::= VariantField { "," VariantField } [ "," ]
VariantField        ::= [ Identifier ":" ] TypeExpression
RecordVariantFields ::= RecordField { "," RecordField } [ "," ]
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
fn eval_int(e: Expr<int>) -> int @Div {
    match e {
        LitInt(n) -> n,
        Add(a, b) -> eval_int(a) + eval_int(b),
        -- LitBool(b) -> 0             -- Error [E0304]: UnreachableMatchArmError: unreachable match arm: constructor 'LitBool' binds T = bool, incompatible with Expr<int>
    }
}

-- Generic GADT evaluator: constructor equations refine return type T:
fn eval<T>(e: Expr<T>) -> T @Div {
    match e {
        LitInt(n) -> n,                -- Refines T ~ int
        LitBool(b) -> b,               -- Refines T ~ bool
        Add(a, b) -> eval(a) + eval(b),-- Refines T ~ int
    }
}
```

#### Constructor-Tuple Equivalence Invariant

Data constructors (algebraic sum type variants and nominal type wrappers) establish a definitional equivalence between comma-separated multi-field declarations and single-tuple payloads:
$$\text{Variant}(T_1, T_2, \dots, T_n) \equiv \text{Variant}((T_1, T_2, \dots, T_n)) \quad (n \ge 0)$$

Ril strictly possesses no 1-element tuples `(T,)` (`(x)` denotes parenthesized grouping; tuples require $\ge 2$ elements; `()` denotes unit). Constructor arity $n$ in expressions and patterns is strictly deterministic:
- **Scope Restriction (Strict Constructor Boundary)**: Equivalence is confined strictly to Data Constructors. Ordinary functions (`fn`), closures, and methods maintain strictly separate parameter lists (`E0314` for an arity mismatch).
- **Positional Tuple Expansion & Literal Compatibility ($n \ge 2$)**: In expression construction and pattern matching, $C(e_1, \dots, e_n)$ and explicit tuple literals $C((e_1, \dots, e_n))$ are definitionally equivalent: outer constructor parentheses absorb inner tuple parentheses.
- **Whole-Tuple Binding or Single Argument ($n = 1$)**: $C(val)$ constructs or matches the scalar payload or whole-tuple object.
- **Unit Payload Constructor ($n = 0$)**: When a variant's payload type is `()`, $C()$ constructs or matches the unit payload directly ($C() \equiv C(())$ ). Bare constructor identifiers without parentheses (e.g. bare `Ok`) are strictly first-class constructor functions (`fn(T) -> Result<T, E>`), and can be bound or passed as function values. Constructing a payload-bearing result still requires a call.
- **Nullary Variant Tag Invariant**: Variants declared without a payload (e.g. `None` in `type Option<T> { Some(T), None }`) are pure zero-field tags: they MUST be written without parentheses (`None`). Supplying argument parentheses to a nullary variant (`None()`) is statically rejected (`E0301`).
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
-- let bad_none = None()                         -- Error [E0301]: TypeMismatchError: variant 'None' has no payload; remove call parentheses

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
-- let sum2 = add(pair)                          -- Error [E0314]: ArityMismatchError: expected 2 arguments, found 1 tuple

-- Nested tuples: non-transitive boundary:
type Node {
    Branch((int, int), str),                     -- Payload is 2-tuple: ((int, int), str)
}
let node = Branch((1, 2), "left")                -- OK: n = 2 arguments
-- let bad_node = Branch(1, 2, "left")           -- Error [E0314]: ArityMismatchError: arity mismatch: expected 2 arguments, found 3
```

### Nominal Type Wrappers

Nominal wrappers encapsulate an underlying type into an isolated nominal identity with zero runtime overhead.

```ebnf
NominalDecl      ::= [ "pub" ] "type" PascalCase [ GenericParams ] [ "(" [ TypeList ] ")" ] [ WhereClause ]
```

When `(TypeExpression)` is omitted, `NominalDecl` defines a **Unit Nominal Type** (e.g. `type Marker`).
- **Memory Layout**: Unit nominal types have a 0-byte memory layout (zero-sized type / ZST).
- **Value Construction**: The bare identifier `Marker` denotes its canonical singleton value (`let m = Marker`).
- **Pattern Matching**: `Marker` acts as a nullary constructor pattern in multi-variant `match` expressions (`match event { Marker -> ... }`). In `let` statements, patterns introducing zero variable bindings (such as `let Marker = m`) are strictly prohibited under the **Non-Vacuous Binding Invariant (`E0309: VacuousBindingError`)**.
- **Prelude Unwrapping**: Unwrapping via `inner(Marker)` evaluates to `()`.
- **Nominal Isolation**: A unit nominal type is an isolated nominal identity, strictly distinct from structural `()`. For example, `Result<Marker, E>` strictly requires `Ok(Marker)` and does NOT permit `Ok()`.

```ril
-- Unit Nominal Types (zero-sized domain markers):
type Marker
type AdminToken

let m: Marker = Marker                 -- OK: bare identifier value construction
let raw_unit: () = inner(m)            -- OK: unwrap unit nominal wrapper evaluates to ()
let _ = m                              -- OK: explicit wildcard discard
-- let Marker = m                      -- Error [E0309]: VacuousBindingError: 'let' pattern must bind at least one variable; nullary constructor 'Marker' introduces zero bindings

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

-- uid == aid                          -- Error [E0305]: NominalTypeMismatchError: mismatched nominal types 'UserId' and 'AccountId'
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
- **Ordinary Clone**: `clone` separates the copy's writable storage from its source, preserving internal aliases and cycles. The receiver may choose immutable publication, read-only `var`, or writable `let mut`/`var mut`. A writable copy with possible internal writable aliases requires the local `^mut` sharing marker; distinct paths inside the copy are not necessarily disjoint.
| Operation | Input | Result |
| :--- | :--- | :--- |
| `clone_immut` | `T` or `Immut<T>` | Independent immutable `Immut<T>` |
| `clone` | `Immut<T>` | Fresh `T`; explicit nested `Immut<U>` fields stay immutable |

Both accept eligible view data and preserve field declarations.
- **Copy Isolation**: Ordinary deep copying does not suspend, invoke user callbacks, or permit an overlapping write during the copy. Both operations preserve the source.
- **Eligibility (`E0530`)**: Check every reachable ordinary constituent. Retained closure environments, scoped resources, tasks, unique receivers, and other non-clonable values cannot be hidden by wrapping or views.
- Immutable environment-free function values are copyable. Opaque resources use only their [explicit contracts](#structured-concurrency-channels).

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
| Array / map | Element and key/value types invariant; fixed lengths must match |
| Tuple | Components invariant; writable access permits slot replacement |
| Sum / nominal arguments | Invariant; transparent aliases retain the expanded type's identity |

Read-only access and Immut qualification add no container subtyping.

### Memory Model and Handle Invariants

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

- **Origins and Permissions**: Binding, projection, wrapping, calls, captures, and returns preserve origins, permissions, and immutable/live status. Alternatives retain all possible origins and only their common permissions. Visible types need not name these facts; [complete provenance](#complete-provenance-and-optional-annotations) remains mandatory.
- **Binding to let (`E0535`)**: Accept immutable data or a fresh ordinary graph without surviving external writers. Reject live views, captured live cells, and mutable environments. Binding neither clones data nor revokes another writer.
- **Local Construction**: A fresh ordinary result may enter `let` when its construction scope or call ends and no external writer or active environment survives. A private fresh result may instead stay writable. Borrowed/external aliases retain their restrictions (`E0528`). Ordinary writable bindings retain their authority until their lexical scope ends; merely having no later textual use does not revoke it. Reassigning `var mut` replaces that binding's path but does not revoke other paths to the old value.
- **Pinned Handles (`E0502`)**: `let mut` and mutable reference parameters cannot be rebound. Their allowed interior writes remain subject to field permissions and exclusivity. `var` may only rebind its slot; `var mut` additionally permits interior writes supplied by its current value. Neither upgrades source permissions.
- **Views**: `let view` grants read-only live observation of stable pinned origins. Scalar projections copy values; reference projections retain live origins. See [Live View Bindings](#live-view-bindings).
- **Authority Use (`E0527`)**: A mutable binding/parameter must perform a write, reassignment, mutable invocation, retention, or authorized transfer on a statically possible path. An annotation or ineffective forwarding alone does not count. This does not require a write on every execution.

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

- **Complete Static Provenance Invariant**: Every storage cell, reference, callable environment, and resource authority MUST retain the possible origins, access permissions, immutable/live facts, alias relationships, retention and escape dependencies, and owning scope/task obligations required by the specified conservative judgments. Completeness means none of those obligations may be erased; it does not require exact prediction of arbitrary run-time paths or object identities. Independent scalar copies retain no reference-sharing authority; capturing a reassignable scalar cell still retains that cell's origin. The same requirement applies through aggregates, projection, branching, recursion, return, higher-order calls, opaque abstraction, handlers, cleanup, and module boundaries.
- **No Semantic Erasure**: An omitted annotation, plain `-> T`, abbreviated callable type, or ordinary call spelling does not discard these facts. Private source names need not become public identifiers; their semantic dependencies still participate in every access and boundary check. Anonymous captures and symbolic callback obligations remain inferred. Named definitions must declare their concrete invocation obligations; no return modes, symbolic callback-forwarding notation, or call-site annotation is required.
- **Conservative Alternatives**: Retain the union of possible origins, accesses, retention, and escape obligations, and only permissions common to all alternatives. Preserve origin relations between inputs and outputs and between output components: a relation established in every retained alternative remains established after the join. Prune only branches excluded by the specified static computations and typing rules. An unproved run-time condition is not evidence of uniqueness or impossible escape. Unknown overlap remains possible overlap; an incomplete proof cannot authorize a loan, immutable publication, or task crossing that requires it.
- **Recursive Dependencies**: Loop and recursive call dependencies retain possible origins and unresolved relationships. A cycle is not evidence of freshness, disjointness, non-escape, termination, or an empty callable row. An obligation may be discharged only by an established fact; unresolved dependencies remain obligations at every affected use. Apply the use's existing diagnostic when its required proof is absent.
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

- **Fresh Evaluation**: Each successful ordinary allocation creates new storage distinct from pre-existing storage. A newly constructed aggregate may still contain references to pre-existing objects; freshness of its outer slots does not establish disjointness of its reachable graph. Each ordinary deep clone creates new writable regions isolated from the source and all pre-existing writable regions, preserving aliases within that one copy. Repeated evaluations of one expression do not denote one shared allocation. Calling an arbitrary function twice does not establish freshness; the function's actual return relation must supply it.

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

Escaped environments and stored writable paths survive their creating scope and still prevent immutable publication. Last-use rules for temporary loans or slice windows do not implicitly consume an ordinary writable binding. Resource consumption follows only its listed contracts.

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

Generics admit type, const-value, and [static-key](#static-key-parameters-and-computed-value-projection) parameters. They apply to data, wrapper, sum, and callable declarations.

```ebnf
GenericParams         ::= "<" GenericParamDecl { "," GenericParamDecl } [ "," ] ">"
GenericParamDecl      ::= TypeParamDecl | ConstParamDecl | StaticKeyParamDecl
TypeParamDecl         ::= PascalCase [ ":" TypeSort ] [ "=" TypeExpression ]
ConstParamDecl        ::= SnakeCase ":" ValueType [ "=" Expression ]
TypeSort              ::= "Type" | KindSignature | RecordConstraint
KindSignature         ::= "Type" "->" ( "Type" | KindSignature )
RecordConstraint ::= "{" [ RecordConstraintField { "," RecordConstraintField } "," ] ".." PascalCase "}"
RecordConstraintField ::= [ "mut" ] Identifier ":" TypeExpression
KeyofConstraint       ::= "keyof" TypeExpression
GenericArgs           ::= "<" GenericArg { "," GenericArg } [ "," ] ">"
GenericArg            ::= TypeExpression | Expression
```

- **Trailing Defaults Invariant (`E0316`)**: If a generic parameter declares a default argument (`= Default`), all subsequent generic parameters in the same parameter list MUST declare default arguments.
- **Telescopic Left-to-Right Scoping Invariant (`E0320`)**: A default argument expression $D_i$ may reference generic parameters declared to its left ($X_1, \dots, X_{i-1}$). Forward references and direct/indirect circular dependencies are statically rejected (`E0320`).
- **Static Value Sorts**: Const parameters admit scalar values and finite immutable aggregate values whose constituents have no resource or callable authority. `ValueType` in the parameter grammar denotes such an admissible value sort, not permission to pass a run-time or live value.
- **Const Generic Evaluation & Purity Invariant (`E0810`, `E0323`)**: Const generic arguments evaluate at compile time within the pure symbolic domain ($\mathbf{Eff} = \emptyset, \mathbf{Cap} = \emptyset$). Non-constant runtime expressions passed to const parameters trigger `E0810`. Arguments failing sort constraints trigger `E0323`.
- **No Untagged Literal Types (`E0318`)**: Concrete values (strings, integers, booleans) cannot serve as bare types. Discrete domain states MUST be modeled via tagged sum types (`type HttpMethod { Get, Post }`). Concrete values enter the type system strictly as compile-time arguments to const parameters (`Buffer<u8, 1024>`, `Matrix<f64, 4>`).
- **Function Generic Default Prohibition (`E0317`)**: Function generic parameters cannot declare defaults (`fn f<T = int>` is rejected); function types are inferred bidirectionally at call sites.

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
-- Error [E0316]: NonTrailingDefaultGenericParamError: generic parameter without default 'U' cannot follow generic parameter with default 'T'

-- Rejection: Forward reference in default argument (E0320):
-- type BadForward<T = U, U = int> = { a: T }
-- Error [E0320]: ForwardTypeDefaultReferenceError: default argument for 'T' contains forward reference to parameter 'U'

-- Rejection: Function generic parameter with default (E0317):
-- fn bad_fn<T = int>(x: T) -> T { x }
-- Error [E0317]: FunctionDefaultGenericProhibitedError: function generic parameter 'T' cannot declare default type; functions rely on caller-site bidirectional inference

-- Rejection: Literal types and untagged unions prohibited (E0318):
-- type BadMethod = "GET" | "POST"
-- Error [E0318]: LiteralTypeProhibitedError: literal values cannot be used as types; declare a tagged sum type instead

-- Rejection: Runtime expression passed to const generic (E0810):
fn check_buf(runtime_size: int) {
    -- let bad_b: Buffer<u8, runtime_size> = Buffer.{ data: [], len: 0 }
    -- Error [E0810]: CallFamilyViolationError: const generic parameter 'cap' expects compile-time constant, found runtime expression 'runtime_size'
}

-- Rejection: Const generic sort mismatch (E0323):
-- let bad_sort: Buffer<u8, "1024"> = Buffer.{ data: [], len: 0 }
-- Error [E0323]: ConstGenericSortMismatchError: const generic parameter 'cap' of sort 'int' supplied with incompatible argument of sort 'str'
```

### Tripartite Ontology and Type Definition Boundaries

Ril establishes a mathematically rigorous, stratified **Tripartite Ontology**, partitioning program semantics across three mutually exclusive domains that converge exclusively at the callable computation arrow:

```
+-----------------------------------------------------------------------------------------------------------------+
|                                             THE TRIPARTITE ONTOLOGY                                             |
+-------------------------------------+-------------------------------------+-------------------------------------+
|  Domain I: Data & Shape (T)         |  Domain II: Storage & Access (C)    |  Domain III: Control & Transfer (E) |
|  - Types at rest                    |  - Storage cell permissions         |  - Stack-delimited control flows    |
|  - Value vs Reference types         |  - Explicit binding permissions     |  - Algebraic effects ('eff')        |
|  - Records, Arrays, Tuples, Sums    |  - Parameter modes ('mut')          |  - Handlers ('with')                |
|  - Nominals & Opaque types          |  - Capability tracking (&mut, &^mut)|  - Affine resumption ('resume')     |
|  - Field 'mut' (interior marker)    |  - Aliasing exclusivity             |  - Built-ins (@Async, @Fiber, @Div) |
+-------------------------------------+-------------------------------------+-------------------------------------+
                                                         |
                                                         v
                                      +-------------------------------------+
                                      |     COMPUTATION CONFLUENCE (fn)     |
                                      |   fn(P) -> R  @Eff  &Cap            |
                                      | - P in T (parameters at rest)       |
                                      | - R in T (return shape at rest)     |
                                      | - @Eff in E (latent control flow)   |
                                      | - &Cap in C (latent access rights)  |
                                      +-------------------------------------+
```

#### The Three Disjoint Semantic Domains

$$\text{Semantic Domains} = \langle \text{Shape (Type)}\ \mathcal{T},\ \text{Access (Capability)}\ \mathcal{C},\ \text{Control (Effect)}\ \mathcal{E} \rangle$$

- **Domain I: Data & Shape Domain ($\mathcal{T}$)**:
   - **Meaning**: Memory representation, data alignment, structural topology, and nominal identity of values in *normal form* (quiescent data at rest).
   - **Syntactic Locus**: Values, expressions, variables, data structures, and function parameter/return types.
   - **Constituents**:
     - *Primitive Value Types*: `bool`, `i8`, `i16`, `i32`, `i64`, `u8`, `u16`, `u32`, `u64`, `int`, `bigint`, `f32`, `f64`, `str`, `bytes`, `()`, `never`.
     - *Heap Reference Types*: Structural records `{...}`, linear arrays `[]T`, associative maps `[K: V]`, anonymous tuples `(...)`, and standard prelude collections (such as `Set<T>`).
     - *Algebraic Sum Types & GADTs*: `type Option<T> { Some(T), None }`.
     - *Nominal Wrappers & Unit Nominals*: `type UserId(int)`, `type Marker`.
     - *Opaque Types*: `pub opaque type SessionToken = str`.
   - **Structural Field Modifier**: The record field modifier `mut` (e.g. `{ mut val: int }`) is strictly an interior mutability layout marker of a heap reference cell. It is **not** an operational capability.
   - **Axiom of Inactivity**: Types are inert shapes. A type cannot perform computation, yield execution control, hold ambient access capabilities, or trigger algebraic side effects.

- **Domain II: Storage & Access Domain ($\mathcal{C}$)**:
   - **Meaning**: Static tracking of heap mutation authority, storage cell access rights, pointer stability, and aliasing exclusivity. It specifies what memory an activation frame or handle is permitted to mutate, reassign, or retain.
   - **Syntactic Locus**: Variable bindings (`let`, `let mut`, `var`, `var mut`, `let view`), parameter/argument modes (`p: T`, `mut p: T`, `^mut p: T`), local `^mut` sharing expressions, and callable capability qualifiers (`&mut`, `&^mut`, `&closure`, `&capture`, global/captured source groups, and named-function state contract references).
   - **Guarantees**: Governed by the Law of Exclusivity, Monotonic Permission Degradation, and Anti-Laundering theorems (`E0520`–`E0528`), preventing hidden aliasing, pointer invalidation, and data races without marker traits or lifetime annotations.
   - **Axiom of Non-Reification**: Capabilities are operational permissions, not data values. A capability cannot be instantiated at runtime, bound to a variable, stored in a collection, or aliased as a standalone type.

- **Domain III: Control & Transfer Domain ($\mathcal{E}$)**:
   - **Meaning**: Dynamic control inversion, delimited continuation interception, stack unwinding protocols, and cooperative fiber scheduling. It specifies what non-local control transfers and ambient runtime requests can occur during expression reduction.
   - **Syntactic Locus**: Exclusively confined to computation / arrow signatures (`fn(P) -> R @Eff &Cap`), effect declarations (`eff`), and handler blocks (`with`).
   - **Constituents**:
     - *Algebraic Effect Definitions*: `eff FileIo { read() -> str }`.
     - *Stack Handlers*: `with Handler { op(args) -> ... }`.
     - *Affine Resumptions*: `resume value`.
     - *Built-in Effect Sub-Lattice*: `@Fiber` (cooperative leaf I/O quantum) $\subset$ `@Async` (compound concurrency alias) $\equiv \lbrace\text{Fiber}, \text{Concurrent}\rbrace$, disjoint from `@Div` (divergence).
   - **Axiom of Delimited Execution**: Effects represent active computational protocols between code and ambient stack handlers. Once an expression is reduced to normal form, its effects have transpired; passive data has no effect annotation of its own; callable constituents retain their latent obligations.

#### The Computation Confluence Point (fn)

The three domains are mutually exclusive and never mix directly. They converge **exclusively** at the first-class callable arrow:

$$\tau_{\text{callable}} = \mathbf{fn}(P_1, \dots, P_n) \to R \ [@\mathcal{E}] \ [\mathbin{\And}\mathcal{C}]$$

```ril
-- The Computation Confluence in Action:
--   Parameters (Domain I: Shape)
--   Return Type (Domain I: Shape)
--   Latent Effects (Domain III: Control)
--   Latent Capabilities (Domain II: Access)
type SocketHandler = fn(mut buffer: []u8, timeout_ms: int) -> Result<int, IoError> @Fiber &mut
```

- **Confluence Semantics**: A function, closure, or thunk is an unevaluated, suspendable computation mediating between input/output data shapes ($P \in \mathcal{T}, R \in \mathcal{T}$), ambient control transfers ($@\mathcal{E} \subseteq \mathcal{E}$), and storage access permissions ($\mathbin{\And}\mathcal{C} \subseteq \mathcal{C}$).
- **First-Class Closure Property**: $\tau_{\text{callable}}$ is a first-class type in Domain I ($\tau_{\text{callable}} \in \mathcal{T}$); callable types can be stored in records, passed as variant payloads, nested in tuples, or aliased under `type T = ...`.

#### Boundaries of Type Definitions

##### Supported Constructs
- **Structural Product Shapes & Interior Mutability**: Record definitions with field-level interior mutability `{ mut val: int, tag: str }`.
- **First-Class Callable Signatures**: Nested function arrows carrying latent effects and capabilities `fn(In) -> Result<Out, Err> @Fiber + Async &mut`.
- **Algebraic Sum Variants & GADTs**: Constructors with positional payloads `Some(T)`, record payloads `Record{ x: int }`, or constructor equations `Lit(int) -> Expr<int>`, including variants holding callable types `Handler(fn(Event) -> () @Io)`.
- **Nominal Wrappers & Unit Nominals**: `type UserId(int)`, `type Marker`.
- **Opaque Type Representations**: `pub opaque type SessionToken = str`.
- **Pure Compile-Time Type Functions**: `halt type Transform<T> = ...` (strictly pure compile-time functions returning `type<T>`).

##### Forbidden Anti-Patterns
Ril statically rejects six structural anti-patterns that attempt to violate domain isolation:

| # | Forbidden Anti-Pattern | Semantic Domain Violation | Diagnostic Code | Diagnostic Identifier |
| :-: | :--- | :--- | :-: | :--- |
| **1** | Bare effect aliases (`type E = @Io`) | Attempting to alias Domain III (Control) as Domain I (Data) | **`E0330`** | `BareEffectTypeAliasError` |
| **2** | Bare capability aliases (`type C = &mut`) | Attempting to alias Domain II (Access) as Domain I (Data) | **`E0331`** | `BareCapabilityTypeAliasError` |
| **3** | Direct variant computation annotations (`type S = Init @Async`) | Injecting Domain II/III onto Domain I data constructor tags | **`E0332`** | `VariantComputationAnnotationError` |
| **4** | Direct field computation annotations (`type C = { f: str @Io }`) | Injecting Domain II/III onto Domain I passive storage slots | **`E0333`** | `FieldComputationAnnotationError` |
| **5** | Generic computation constraints (`<T: @Io>`, `<T: &mut>`) | Constraining Domain I type parameters by Domain II/III | **`E0334`** | `GenericComputationConstraintError` |
| **6** | Type function computation annotations (`halt type F<T> = ... @Io`) | Polluting compile-time symbolic evaluation with runtime effects/caps | **`E0335`** | `TypeFunctionComputationAnnotationError` |

#### Code-First Normative Rules and Contrast Matrix

```ril
-- Bare Effect Aliases (E0330) vs. 'eff' Declarations:
-- type BadEffect = @Io                         -- Error [E0330]: BareEffectTypeAliasError: bare effect '@Io' cannot be aliased as a type; declare effects using 'eff'
-- type CombinedEffect = @Io + Async            -- Error [E0330]: BareEffectTypeAliasError: bare effect row '@Io + Async' cannot be aliased as a type; combine effects via 'eff'
-- type DynamicEff = @Fiber                     -- Error [E0330]: BareEffectTypeAliasError: bare effect '@Fiber' cannot be used in type definition

eff Io {
    read_line() -> str,
    write_line(str) -> (),
}

eff AsyncIo { Io, Fiber }                      -- OK: effect set combination declared via 'eff'
type ReaderFn = fn() -> str @Io                -- OK: effect annotates callable arrow
type AsyncWorker<T> = fn(T) -> () @AsyncIo     -- OK: effect annotates callable arrow

-- Bare Capability Aliases (E0331) vs. Interior Mutability Markers:
-- type BadMut = &mut                           -- Error [E0331]: BareCapabilityTypeAliasError: bare capability '&mut' cannot be aliased as a type; capabilities belong to storage and callable domains
-- type BadShare = &^mut                        -- Error [E0331]: BareCapabilityTypeAliasError: bare capability '&^mut' cannot be aliased as a type
-- type BadGlobal = &{mut app_cache}            -- Error [E0331]: BareCapabilityTypeAliasError: bare capability '&{mut app_cache}' cannot be aliased as a type
-- type BadClosure = &closure                   -- Error [E0331]: BareCapabilityTypeAliasError: bare capability '&closure' cannot be aliased as a type

type StateNode = {
    mut count: int,                            -- OK: field 'mut' is a structural layout marker, not a capability
    tag: str,
}
type Mutator<T> = fn(mut target: T) -> () &mut -- OK: capability annotates callable arrow
type SharedLogger = fn(str) -> () &closure &^mut -- OK: capability annotates callable arrow

-- Sum Variant Computation Annotations (E0332) vs. Callable Payloads:
-- type TaskStatus {
--     Pending,
--     Running @Async,                         -- Error [E0332]: VariantComputationAnnotationError: sum variant 'Running' cannot declare algebraic effect '@Async'; variants are data constructors, not computations
--     Mutating &mut,                          -- Error [E0332]: VariantComputationAnnotationError: sum variant 'Mutating' cannot declare state capability '&mut'; variants are data constructors, not computations
--     Suspended(int) @Fiber,                  -- Error [E0332]: VariantComputationAnnotationError: sum variant 'Suspended' cannot declare algebraic effect '@Fiber'
-- }

type TaskStatus {
    Pending,                                   -- OK: nullary data constructor tag
    Running(fn() -> () @Async),                -- OK: payload is a callable arrow encapsulating computational effect
    Mutating(fn(mut StateNode) -> () &mut),    -- OK: payload is a callable arrow encapsulating mutation capability
    Suspended({ duration_ms: int }),           -- OK: pure record payload
    Completed(int),                            -- OK: pure scalar payload
}

let status: TaskStatus = Running(\-> {
    Async::sleep(100)
})                                             -- OK: constructs data variant holding callable thunk

-- Record Field Computation Annotations (E0333) vs. Callable Fields:
-- type BadChannel = {
--     stream: str @Io,                        -- Error [E0333]: FieldComputationAnnotationError: record field 'stream' cannot declare algebraic effect '@Io'; fields store values or callables
--     buffer: []u8 &mut,                      -- Error [E0333]: FieldComputationAnnotationError: record field 'buffer' cannot declare state capability '&mut'; use 'mut' prefix or callable arrow
--     sink: int &{mut app_cache},             -- Error [E0333]: FieldComputationAnnotationError: record field 'sink' cannot declare external state capability
-- }

type ValidChannel = {
    mut buffer: []u8,                          -- OK: 'mut' prefix marks heap interior mutability
    stream: fn() -> str @Io,                   -- OK: field stores a callable arrow carrying algebraic effect
    writer: fn(mut []u8) -> () &mut,           -- OK: field stores a callable arrow carrying state capability
}

let mut ch = ValidChannel.{
    buffer: [],
    stream: \-> Io::read_line(),
    writer: \mut buf -> { buf !> Array::push(0) },
}
ch.buffer !> Array::push(42)                   -- OK: mutate interior mutable field via 'let mut' root

-- Generic Computation Constraints (E0334) vs. Automatic Forwarding:
-- fn bad_exec<T: @Io>(task: T) -> () { task() } -- Error [E0334]: GenericComputationConstraintError: generic parameter 'T' cannot be constrained by algebraic effect '@Io'; generics parameterize types or values
-- type BadWrapper<T: &mut> = { item: T }      -- Error [E0334]: GenericComputationConstraintError: generic parameter 'T' cannot be constrained by state capability '&mut'
-- fn bad_pipe<T: @Async + Io>(x: T) -> T { x } -- Error [E0334]: GenericComputationConstraintError: generic parameter 'T' cannot be constrained by effect row '@Async + Io'

fn execute<T, R>(task: fn(T) -> R, arg: T) -> R {
    task(arg)                                  -- OK: automatically forwards callee's effects and capabilities
}
fn log_id<T: { id: int, ..R }>(item: T) -> int {
    item.id                                    -- OK: row constraint is a shape property
}
fn get_field<T: { ..R }, K: keyof T>(record: T, key: K) -> T.(K) {
    record.(key)                               -- OK: keyof constraint is a shape property
}

-- Pure Type Function Computation Annotations (E0335) vs. Symbolic Purity:
-- halt type BadTransform<T> = \T -> type<T> @Io -- Error [E0335]: TypeFunctionComputationAnnotationError: pure type function cannot declare algebraic effect '@Io'; type functions are axiomatically pure
-- type BadMapper<T> = \T -> type<T> &mut       -- Error [E0335]: TypeFunctionComputationAnnotationError: pure type function cannot declare state capability '&mut'
-- halt type BadAsyncType<T> = \T -> type<T> @Async &closure -- Error [E0335]: TypeFunctionComputationAnnotationError: pure type function cannot declare effects or capabilities

halt type MakeNullable = \T -> type<?T>        -- OK: pure type evaluation returning type<T>
halt type SafeRecord = \T -> {
    if type<T> == type<int> {
        type<{ val: int, valid: bool }>
    } else {
        type<{ val: T, valid: bool }>
    }
}
type NullableInt = MakeNullable<int>           -- Resolves to ?int
type IntRecord   = SafeRecord<int>             -- Resolves to { val: int, valid: bool }
```

#### The Asymmetric Scope of Influence

##### Capabilities Govern Bindings
Binding and origin permissions govern:
- **Reassignment Privilege**: Whether a binding slot can be overwritten (`var` / `var mut` vs `let` / `let mut`).
- **Interior Write Privilege**: Whether fields reachable through a handle can be mutated in place (`let mut` / `var mut` vs `let` / `let view` / plain `var`).
- **Live Observation**: Whether a handle dynamically observes background mutations of an aliased heap object (`let view`).
- **Anti-Laundering Degradation**: Enforcing monotonic permission degradation ($\text{Mut} \succ \text{ReadOnly} \succ \text{None}$) across destructuring patterns, container insertions, and returns (`E0520`–`E0528`).

##### Algebraic Effects Never Govern Bindings (Function & Data Colorlessness)
Algebraic effects govern dynamic, non-local control transfers during expression evaluation:
- When an effectful operation is evaluated (`Console::print("hi")`, `Yield::emit(x)`), it traverses up the dynamic execution stack to find an active enclosing `with` handler.
- Upon reduction to normal form, all effect operations have already been dispatched and handled.
- The resulting passive data has no direct effect annotation. Any callable constituent retains the effects of its future invocation.
- Value bindings, record fields, tuple components, and array elements are strictly colorless. Decorating value bindings with `@Eff` triggers `E0613: ValueEffectAnnotationError`.

##### The Intersecting Boundary: Capability-Bearing Effect Operations
The tripartite domains intersect cleanly in capability-bearing effect operations, where control routing and memory mutation rights are orthogonal:

```ril
eff BufferIo {
    read_into(mut buf: []u8) -> int &mut,       -- Operation demands in-place buffer mutation
}
```
- The effect tag `BufferIo` governs **Control** (Domain III: who intercepts the operation up the call stack).
- The capability annotation `&mut` governs **Access** (Domain II: the operation demands write authority into caller-supplied storage).

#### Tripartite EBNF Grammar Formalization

```ebnf
(* ========================================================================= *)
(* 1. TYPE EXPRESSIONS (Domain I: Data & Shape)                              *)
(* ========================================================================= *)

TypeDecl         ::= [ "pub" ] [ "halt" ] "type" PascalCase [ GenericParams ] [ WhereClause ] "=" TypeExpression
OpaqueTypeDecl   ::= [ "pub" ] "opaque" "type" PascalCase [ GenericParams ] [ WhereClause ] "=" TypeExpression
(* NominalDecl is defined in its earlier grammar production. *)
(* SumTypeDecl is defined in its earlier grammar production. *)

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
(* ArrayType is defined in its earlier grammar production. *)
(* MapType is defined in its earlier grammar production. *)
(* TupleType is defined in its earlier grammar production. *)

(* Callable Type: THE COMPUTATION CONFLUENCE POINT *)
CallableType     ::= "fn" "(" [ ParameterTypeList ] ")" [ "->" TypeExpression ] [ EffectAnnot ] [ StateAnnot ]
ParameterTypeList::= ParameterTypeItem { "," ParameterTypeItem } [ "," ]
ParameterTypeItem ::= [ ParameterMode ] [ SnakeCase ":" ] TypeExpression

(* Records: 'mut' is exclusively an interior field layout marker *)
(* RecordType is defined in its earlier grammar production. *)
RecordFieldList  ::= ".." PascalCase | RecordField { "," RecordField } [ "," [ ".." PascalCase ] ]
(* RecordField is defined in its earlier grammar production. *)

(* Sum Types: Variants are pure data constructors *)
VariantDeclList  ::= VariantDecl { "," VariantDecl } [ "," ]
(* VariantDecl is defined in its earlier grammar production. *)
VariantPayload   ::= "(" [ VariantFields ] ")" | "{" [ RecordFieldList ] "}"
(* VariantFields is defined in its earlier grammar production. *)
(* VariantField is defined in its earlier grammar production. *)

(* Generic Parameters: Strictly Types or Const Values *)
(* GenericParams is defined in its earlier grammar production. *)
(* GenericParamDecl is defined in its earlier grammar production. *)
(* TypeParamDecl is defined in its earlier grammar production. *)
(* ConstParamDecl is defined in its earlier grammar production. *)
(* TypeSort is defined in its earlier grammar production. *)
(* KindSignature is defined in its earlier grammar production. *)
(* RecordConstraint is defined in its earlier grammar production. *)
(* RecordConstraintField is defined in its earlier grammar production. *)
(* KeyofConstraint is defined in its earlier grammar production. *)

(* ========================================================================= *)
(* 2. CONTROL & TRANSFER DOMAIN (Domain III: Algebraic Effects)              *)
(* ========================================================================= *)

EffectDecl       ::= [ "pub" ] "eff" PascalCase [ GenericParams ] "{" EffectMemberList "}"
EffectMemberList ::= EffectOpDecl { "," EffectOpDecl } [ "," ] | EffectIdentifier { "," EffectIdentifier } [ "," ]
EffectOpDecl     ::= SnakeCase "(" [ ParameterTypeList ] ")" [ "->" TypeExpression ] [ StateAnnot ]
EffectAnnot      ::= "@" ( EffectRow | "{" "}" )
EffectRow        ::= EffectIdentifier { "+" EffectIdentifier }
EffectIdentifier ::= QualifiedName [ GenericArgs ]

(* ========================================================================= *)
(* 3. STORAGE & ACCESS DOMAIN (Domain II: Capabilities)                      *)
(* ========================================================================= *)

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

The contextual `closure` group header takes precedence over the global-list production. A captured group requires at least one item: `&{closure,}` is `E0538`, while `&{closure}` reads a global binding named `closure`. Built-in `&mut`, `&^mut`, `&capture`, and `&closure` retain their meanings ahead of the reference production. A state contract reference is permitted only on an ordinary named function definition, subject to [its reference rules](#named-function-state-contract-references); the common grammar does not authorize it in other annotation positions.

```ril
type DeferredFactory = fn() -> fn() -> int @Io -- Io belongs to the returned callable
type EffectfulFactory = fn() -> (fn() -> int) @Io -- Io belongs to the factory
type CapturingFactory = fn() -> (fn() -> int &closure) &capture
```

Arrows associate right; effect/state suffixes bind to the nearest callable not closed by parentheses. Omitted returns mean `-> ()` on named functions, callable types, and effect operations. Anonymous results are inferred.

---

The productions below supply shared declaration vocabulary. An omitted callable row preserves inferred obligations in type expressions; explicit empty rows close that domain. `key: K` is a static-argument form only when K was declared with `keyof`.

```ebnf
ParameterMode    ::= "mut" | "^mut"
StaticKeyParamDecl ::= PascalCase ":" KeyofConstraint [ "=" Expression ]
ValueType        ::= TypeExpression
TypeList         ::= TypeExpression { "," TypeExpression } [ "," ]
FieldLabel       ::= SnakeCase | SuppressedVar | PascalCase
LocalTypeDecl    ::= TypeDecl | OpaqueTypeDecl | NominalDecl | SumTypeDecl
WhereClause      ::= SignatureWhereClause
ReturnType       ::= "->" TypeExpression
TypeReference    ::= QualifiedName [ GenericArgs ]
QualifiedName    ::= Identifier { "::" Identifier }
PrimitiveType    ::= "bool" | "i8" | "i16" | "i32" | "i64" | "int"
                  | "u8" | "u16" | "u32" | "u64" | "bigint"
                  | "f32" | "f64" | "str" | "bytes" | "(" ")" | "never"
TypeFunctionExpr ::= "\" TypeFnParam { "," TypeFnParam } "->" Expression
TypeFnParam      ::= StaticKeyParamDecl
                  | PascalCase [ ":" TypeSort ] [ "=" TypeExpression ]
                  | SnakeCase ":" TypeExpression [ "=" Expression ]
MetaLetDecl      ::= "meta" "let" ( ScreamingSnakeCase | "_" ) [ ":" TypeExpression ] "=" Expression
MetaFnDecl       ::= [ "pub" ] "meta" "fn" SnakeCase [ GenericParams ] "(" [ ParameterList ] ")" ReturnType Block
```

The casing, static-sort and parameter-mode constraints apply in addition to these productions. In particular, PascalCase field labels require a mapped schema, effect names resolve to PascalCase effect declarations, and mutable modes do not apply to static key arguments.

---

#### Shared Expression and Pattern Vocabulary

Operator precedence resolves expression nesting. Lexical character classes use regular-expression notation; other square brackets mean optional syntax.

Character categories follow their literal sections and exclude unescaped closing delimiters. `Newline` and `EOF` mean line end and source end.

```ebnf
Digit           ::= [0-9]
HexDigit        ::= [0-9a-fA-F]
OctalDigit      ::= [0-7]
BinaryDigit     ::= "0" | "1"
Literal         ::= IntLiteral | FloatLiteral | StringLiteral | RawStringLiteral
                  | ByteStringLiteral | "true" | "false" | "(" ")"
Expression      ::= Literal | QualifiedName [ GenericArgs ] | "(" Expression ")"
                  | TupleExpr | RecordExpr | ArrayExpr | MapExpr | Block
                  | CallExpr | AnonFnExpr | AccessorExpr | MatchExpr | TypeMatchExpr
                  | IfExpr | LoopExpr | WhileExpr | ForExpr | ControlTransfer
                  | ResumeExpr | AssignmentExpr | UnaryExpr | BinaryExpr | SharingExpr
                  | MemberExpr | IndexExpr | RangeExpr | IsExpr
                  | Expression "?" | "type" "<" TypeExpression ">" | "keyof" TypeExpression
TupleExpr       ::= "(" Expression "," Expression { "," Expression } [ "," ] ")"
RecordExpr      ::= [ TypeReference ] ".{" [ RecordValueField { "," RecordValueField } [ "," ] ] "}"
RecordValueField ::= FieldLabel [ ":" Expression ] | ".." Expression
ArrayExpr       ::= "[" [ Expression { "," Expression } [ "," ] ] "]"
MapExpr         ::= "[" ":" "]" | "[" MapEntry { "," MapEntry } [ "," ] "]"
MapEntry        ::= Expression ":" Expression
IfExpr          ::= "if" Expression Block [ "else" ( Block | IfExpr ) ]
UnaryExpr       ::= ( "-" | "!" | "~" ) Expression
SharingExpr     ::= "^mut" Expression
BinaryExpr      ::= Expression BinaryOperator Expression
BinaryOperator  ::= "*" | "/" | "%" | "/?" | "%?" | "*%" | "+" | "-" | "+%" | "-%"
                  | "<<" | ">>" | "&" | "^" | "|" | "==" | "!=" | "<" | "<=" | ">" | ">="
                  | "in" | "&&" | "||" | "??" | "|>" | "!>"
MemberExpr      ::= Expression ( "." | "?." ) ( FieldLabel | TupleIndex )
                  | Expression "." "(" Expression ")"
IndexExpr       ::= Expression ( "[" | "?[" ) Expression "]"
RangeExpr       ::= [ Expression ] ( ".." | "..=" ) [ Expression ]
IsExpr          ::= Expression "is" OrPattern [ "if" Expression ]
AssignmentExpr  ::= AssignTarget AssignmentOperator Expression
AssignTarget    ::= QualifiedName | Expression "." ( FieldLabel | TupleIndex | "(" Expression ")" )
                  | Expression "[" Expression "]"
AssignmentOperator ::= "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "+%=" | "-%=" | "*%="
                     | "&=" | "|=" | "^=" | "<<=" | ">>="
Separator       ::= ";" | Newline
NumericPattern  ::= [ "-" ] ( IntLiteral | FloatLiteral )
LiteralPattern  ::= Literal | NumericPattern
WildcardPattern ::= "_"
RangePattern    ::= NumericPattern ( ".." | "..=" ) NumericPattern
RigidNominalPattern ::= QualifiedName [ "<" TypePatternInner { "," TypePatternInner } [ "," ] ">" ]
PrimitivePattern ::= PrimitiveType
ArrayPattern    ::= "[" [ Expression ] "]" TypePatternInner
MapPattern      ::= "[" TypePatternInner ":" TypePatternInner "]"
TypeRecordPattern ::= "{" [ TypePatternField { "," TypePatternField } [ "," TypeRestPattern ] [ "," ] ] "}"
TypePatternField ::= [ "mut" ] FieldLabel ":" TypePatternInner
TypeTuplePattern ::= "(" ")" | "(" TypePatternInner "," ( TypeRestPattern | TypePatternInner { "," TypePatternInner } [ "," TypeRestPattern ] [ "," ] ) ")"
TypeRestPattern ::= ".." "let" PascalCase
```

- Only slices permit omitted range endpoints.
- Assignment is non-associative; chained assignment is rejected.
- `^mut` is a prefix sharing expression at unary precedence. It evaluates its operand once and preserves that value's identity and permissions; its permitted uses are defined under [Retained Mutable Sharing](#retained-mutable-sharing). It is not a first-class capability value.
- Type patterns use type-specific products. Bare literals are allowed only in const-argument positions.
- Comments and literal delimiters follow lexical rules.
- Numeric patterns use the scrutinee's numeric type and the same representability rules as numeric expressions. Range patterns require integer endpoints of that type with `lower <= upper`; an equal-bound closed range matches one value and an equal-bound half-open range matches none. Arbitrary computed expressions are not literal patterns (`E0301`).

## Declarations and Bindings

### Binding Permissions and Storage Matrix

| Binding | Slot reassignment | Writes through this binding | Data guarantee |
| :--- | :---: | :--- | :--- |
| `let` | No | No | Entire ordinary reachable graph immutable; sharing permitted |
| `let mut` | No | Granted interior/environment writes | Pinned reference; not necessarily unique |
| `var` | Yes | No interior/environment writes | Referenced data remains read-only; immutable/live facts are preserved |
| `var mut` | Yes | Granted interior/environment writes | Each assigned value must supply write authority; no permission upgrade |
| `let view` | No | No | Live observation of stable permitted origins; not immutable |

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

```ebnf
LetDecl ::= [ "pub" ] "let" Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
```

```ril
let x = 10                             -- Immutable integer binding
let (a, b) = (1, 2)                    -- Destructuring tuple binding
-- x = 20                              -- Error [E0501]: ImmutableReassignmentError: cannot reassign immutable binding 'x'

type Config = { capacity: int, items: []int }
let cfg = Config.{ capacity: 64, items: [] }
let .{ var capacity, items: _ } = cfg
capacity += 1                         -- OK: independent scalar copy
-- let .{ capacity: _, mut items } = cfg -- Error [E0521]: immutable reference cannot acquire write permission
```

### Pinned Mutable Handles

A binding declared with `let mut` binds a reference-type heap object as a **pinned mutable handle**. It permits in-place mutation of fields and elements, but statically forbids handle reassignment (`E0502`).

#### Normative Rules for Pinned Handles
- **Pinned Handle Invariant (`E0502`)**: A `let mut` handle is permanently pinned to its initial heap allocation. Reassigning the identifier (`handle = new_obj`) is statically rejected under `E0502: PinnedHandleReassignmentError`.
- **Value Type Prohibition (`E0402`)**: Primitive value types (`int`, `bool`, `f64`, etc.) have no interior mutable fields. Declaring a value type as `let mut` is statically rejected under `E0402: ValueTypePinnedMutError`; mutable value types MUST be declared with `var`.
- **Live View Stability**: Pinned mutable handles provide guaranteed pointer stability as mutable roots for live views (`let view`).

```ebnf
LetMutDecl ::= "let" "mut" Pattern [ ":" TypeExpression ] "=" Expression
```

```ril
type Buffer = { mut items: []int }
let mut buf = Buffer.{ items: [1, 2] }

-- In-place interior mutation is permitted:
buf.items !> Array::push(3)            -- OK: in-place write to pinned buffer

-- Handle reassignment is statically rejected:
-- buf = Buffer.{ items: [] }          -- Error [E0502]: PinnedHandleReassignmentError: use 'var mut' for both reassignment and interior writes

-- Value types under let mut are rejected:
-- let mut count: int = 0              -- Error [E0402]: ValueTypePinnedMutError: value type 'int' has no interior mutability; use 'var'

-- Pattern-level pinned mutable destructuring:
type NodePair = { mut left: Buffer, mut right: Buffer }
let mut pair = NodePair.{ left: Buffer.{ items: [] }, right: Buffer.{ items: [] } }
let .{ mut left, mut right } = ^mut pair
left.items !> Array::push(10)          -- OK: pinned mutable handle
right.items !> Array::push(20)         -- Both destructured authorities are exercised
-- left = Buffer.{ items: [] }        -- Error [E0502]: PinnedHandleReassignmentError: cannot reassign pinned handle 'left'

-- Definite Mutation Invariant:
-- let mut unused = Buffer.{ items: [] } -- Error [E0527]: UnusedMutableBindingError: variable 'unused' declared 'let mut' but never modified in-place
```

### Reassignable Mutable Variables

A binding declared with `var` establishes a **reassignable variable cell**. Plain `var` permits slot reassignment (`x = ...`), but grants only read-only access to referenced data. `var mut` additionally permits interior or callable-environment writes supported by the assigned value.

#### Normative Rules for Reassignable Variables
- **Separate Permissions**: `var` controls its slot only. A reference in plain `var` cannot provide `mut`/`^mut` arguments or invoke a mutable environment (`E0520`). `var mut` controls both its slot and the granted interior permissions; field and constituent permissions still apply.
- **Monotonic Anti-Laundering (`E0520`)**: Initializing or assigning `var mut` from a read-only reference is rejected. Adding `mut` never upgrades the value. Every assignment preserves its actual origin and is checked anew; a local additional writable alias requires `^mut`.
- **Value Types (`E0402`)**: Scalars use plain `var`; `var mut` requires reference data or a writable callable environment.
- **Read-Only Live Values**: Plain `var` may hold a live read-only reference without making it immutable. Neither `var` nor `var mut` is a stable origin for `let view` (`E0531`), including through intermediate aliases.
- **Authority Use (`E0527`)**: Plain `var` must exercise reassignment on a statically possible path. `var mut` must exercise both its reassignable slot and its interior/environment authority; use `let mut` when only pinned interior authority is needed. Uses are checked as specified in [Memory Model and Handle Invariants](#memory-model-and-handle-invariants).

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
-- cursor.val = 99                     -- Error [E0520]: MutabilityLaunderingError: cannot mutate field 'val' through read-only handle 'cursor'

-- Pattern-level var destructuring:
var (start_idx, end_idx) = (0, 10)
start_idx += 1; end_idx -= 1           -- OK: both variables reassignable

-- Definite Mutation Invariant:
-- var unused_var = 100                -- Error [E0527]: UnusedMutableBindingError: variable 'unused_var' declared 'var' but never modified or reassigned
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
-- let scoped scalar = 42              -- Error [E0301]: no cleanup contract
```

#### Normative Rules for Scoped Bindings

| Concern | Rule |
| :--- | :--- |
| Ordinary resource | Accessible `on_close: fn() -> ()` required (`E0301`) |
| Opaque resource | Requires an explicit scoped-cleanup contract; opacity alone supplies none (`E0301`) |
| Registration | After successful initialization; per binding and per loop activation; failed initialization registers nothing |
| Exit | Invoke once in reverse registration order, including cancellation/abort; double-fault exception below |
| Callback selection | Read the current `on_close` at exit; retain no earlier snapshot. Opaque resources use their specified action |
| Initialization/replacement | Preserve cleanup eligibility and permissions; no residual effects (`E0616`) or Div (`E0617`) |
| Mutable cleanup environment | Requires `let scoped mut` and a mutable `on_close` field; cleanup invocation satisfies `E0527` |
| Other binding modes | Plain `let scoped` requires immutable data; rebinding: `E0502`; `var`/`var mut`: `E0532` |
| Invocation | Internal handlers and permitted writes allowed; check exclusivity then, not as a continuous registration loan |
| Escape | Views, closures, containers, and transfer cannot carry scoped authority out (`E0604`); detached ordinary-data copies are exempt |
| Children | Finish before cleanup of resources they could access |

| Cleanup panic occurs during | Outcome |
| :--- | :--- |
| Normal exit | Begin panic unwinding of remaining resources |
| Panic, cancellation, or abort | Record both causes; abandon remaining cleanup in the failed frame |

Abandoned computations cannot resume. A double fault reports `DoubleFaultFatal` to its task or aborts an unsupervised program; pure parallel branches use [reference visibility](#canonical-leftmost-panic-precedence-rule).

```ebnf
ScopedDecl ::= "let" "scoped" [ "mut" ] Identifier [ ":" TypeExpression ] "=" Expression
```

### Live View Bindings

```ebnf
LetViewDecl ::= "let" "view" Identifier [ ":" TypeExpression ] "=" Expression
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
let snapshot = clone_immut(observed)   -- OK: snapshot, not a live alias
```

- **Origins (`E0531`)**: Require a live pinned origin (`let mut`, `mut`, or `^mut`), including provenance-preserving projections, returns, aggregates, views, and observer closures. Reject `var`/`var mut` origins and immutable-only inputs; indirection cannot hide them.
- **Single Evaluation**: Keep the initializer's resulting reference, not a reactive expression. Replacing `parent.child` leaves an existing child view observing the old object. Reachable data outlives the root identifier.
- **Observer Closure**: It may read pinned live origins but cannot write captures. Effects remain independent obligations; read-only observation needs no artificial mutation for `E0527`.
- **Permissions**: A view cannot supply `mut`/`^mut` or become immutable through aliasing. Scalars copy independently; references keep their origins. Eligible view data supports `clone`/`clone_immut`, but not `derive`.
- **Task Confinement (`E0601`)**: A live view, or any closure/container containing it, cannot cross a concurrent task boundary. Immutable snapshots can cross it.

```ril
type Parent = { mut child: Cell }
let mut parent = Parent.{ child: Cell.{ count: 1 } }
let view child = parent.child
parent.child = Cell.{ count: 9 }
assert(child.count == 1)                -- Keeps the original child, not a reactive projection
```

### Type Declarations and Opaque Types

```ebnf
(* TypeDecl is defined in its earlier grammar production. *)
(* OpaqueTypeDecl is defined in its earlier grammar production. *)
```

```ril
-- Transparent Type Declarations:
pub type AccountId = int              -- Direct type alias, transparent across module boundaries
type Point = { x: int, y: int }        -- Local record type alias

-- Cyclic structural type alias rejection (E0313):
-- type BadCyclicA = { following: BadCyclicB }
-- type BadCyclicB = { prev: BadCyclicA } -- Error [E0313]: CyclicTypeAliasError: structural type aliases 'BadCyclicA' and 'BadCyclicB' form a cyclic dependency without nominal or sum indirection

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

-- let bad_top_token = create_token("secret_token_1234")? -- Error [E0205]: QuestionMarkOutsideFunctionError: postfix '?' operator used outside function or closure body; no enclosing activation frame to receive early return

fn authenticate_client() -> ?SessionToken {
    let token = create_token("secret_token_1234")? -- OK: propagated via '?' inside function frame

    -- External boundary invariants:
    -- let bad_assign: SessionToken = "raw" -- Error [E0301]: TypeMismatchError: expected opaque 'SessionToken', found 'str'
    -- let bad_unfold: str = token         -- Error [E0301]: TypeMismatchError: cannot implicitly convert opaque 'SessionToken' to 'str'
    -- let bad_inner = inner(token)        -- Error [E0308]: OpaqueBoundaryViolationError: 'inner()' cannot penetrate opaque type 'SessionToken' (requires type W(T))
    -- let SessionToken(s) = token         -- Error [E0308]: OpaqueBoundaryViolationError: opaque type 'SessionToken' does not expose a pattern deconstructor

    -- Valid external operations:
    let same_eq = (token == token)         -- OK: same-type equality permitted when underlying type supports '=='
    -- let cross_eq = (token == "raw")     -- Error [E0301]: TypeMismatchError: cannot compare distinct types 'SessionToken' and 'str'

    -- Operations via explicit exports & pipeline:
    let raw_str = token |> reveal_token()  -- OK: explicit deconstruction via exported function

    -- Zero runtime boxing: storage in collections carries zero wrapper allocation:
    let active_tokens: []SessionToken = [token]
    let token_map: [SessionToken: int] = [token: 42]

    Some(token)
}
```

### Effect Declarations

```ebnf
(* EffectDecl is defined in its earlier grammar production. *)
(* EffectOpDecl is defined in its earlier grammar production. *)
```

```ril
eff Console {
    print(str) -> (),
    read_line() -> str,
}

eff State<S> {
    get() -> S,
    put(val: S) -> (),
}

eff AppEffects { Console, State<int> } -- Combined effect set
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
- **Hard Safety Membrane Invariant**: Invocations across `.d.ril` external boundaries are strictly sealed against unhandled host faults. External traps or host exceptions never corrupt caller stack frames; they resolve either to domain error variants (`Result<T, E>`) or deterministic runtime panics contained at `scope` boundaries.
- **Ordinary Exchange**: Ordinary inputs, outputs, and constants must be scalars or deeply immutable ordinary data with no surviving foreign writer. They cannot contain live views, callables, tasks, or resources. This excludes even immutable environment-free function values: only a separate callback parameter receives the temporary callback contract below. An immutable returned graph may share immutable storage; a plain return type does not establish freshness or write permission (`E0528`).
- **Temporary Callbacks**: A separately declared callback parameter may be invoked only during the current foreign call and on the current Ril task. Its actual effects, access origins, environment permissions, and exclusivity obligations remain in force. A mutable callback requires the existing `mut` parameter/argument mode. The foreign side cannot inspect its environment, retain or return it, or send it to another task under this default contract. Every callback argument and result must itself satisfy the ordinary exchange or listed resource rules; temporary callback permission is not an exemption for mutable ordinary data or nested callable exchange.
- **Listed Resource Contracts (`E0908`)**: Only resource operations explicitly specified here may extend those exchange rules. Opaque declarations, `@Fiber`, `mut`, and `^mut` do not by themselves authorize resource mutation, callback retention, copying, closing, or transfer. Requests outside the default or a listed contract are rejected. Ordinary Ril opaque types still preserve their actual data provenance and acquire no resource exemption.
- **Trusted Boundary**: An external entity's conformance to its declared exchange and effect contracts is a trusted premise. Static checking establishes the Ril program's compliance with those contracts, not the truth of an implementation whose body is absent. Diagnostic explanations identify the foreign contract as the origin of such facts; missing authority is never replaced by an assumption of freshness or safety.

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
-- pub fn bad_body() -> int { 42 }     -- Error [E0901]: BodyInDeclModuleError: functions in '.d.ril' cannot have an implementation body
-- pub let BAD_CONST: int = 100        -- Error [E0901]: BodyInDeclModuleError: constants in '.d.ril' cannot have an initializer expression

-- Opaque penetration prohibited (E0907):
-- fn test_penetrate(elem: DomElement) {
--     let id = elem.id                 -- Error [E0907]: ForeignStructuralFieldPenetrationError: cannot access field on opaque type 'DomElement'
-- }

-- Missing body in standard .ril module (E0902):
-- In file: platform/dom.ril (standard module)
-- fn unimplemented_render(elem: DomElement) -> () -- Error [E0902]: MissingBodyInStandardModuleError: function 'unimplemented_render' declared in standard '.ril' module must have an implementation body
```

The DOM contract above admits read-only `DomWindow`/`DomElement` resource descriptors, the `WINDOW` constant, and the two displayed operations. Repeated queries may designate the same external object; a stable descriptor does not make that object immutable. These operations grant no ordinary write authority, clone/transfer permission, or permission to pass a descriptor to another task. Attribute results are ordinary immutable data. Mutation and retained listener registration have no contract in this list.

```ril
-- In file: platform/text.d.ril; default ordinary exchange and temporary callback contracts:
pub fn get_data() -> []int
pub fn transform_text(text: str, transform: Transformer) -> str
where
    type Transformer = fn(str) -> str @{} &{}

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
| Wrapping arithmetic | Fixed-width integers only (`E0301` otherwise); reduce modulo their representation |
| Fixed-width shifts | Panic for count < 0 or >= bit width; left discards high bits, signed right extends sign, unsigned right is logical |
| `bigint` | No arithmetic overflow; negative shift counts panic; bitwise operations use unbounded two's complement |

| Floating-point property | Rule |
| :--- | :--- |
| Precision | IEEE 754 widths; round each operation to nearest, ties to even; no implicit fusion |
| Special values | Preserve subnormals and signed zero; use canonical quiet NaNs |
| Overflow / division by zero | Infinity or NaN, without panic |
| Decimal literals | Round once to the contextual floating type |
| Safe division/remainder | `None` for a zero divisor; otherwise retain the IEEE result |
| Remainder | Truncating remainder |

The pointer-sized `int` has target-dependent range; fixed-width guarantees do not fix its overflow boundary.

### Bitwise and Shift Operators

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

-- Pattern matching test via 'is' (evaluated as bool, bindings scoped to guard):
let opt: ?int = Some(42)
let matches = opt is Some(x) if x > 0  -- true; 'x' is scoped strictly to guard expression
```

```ril
assert([1, 2] == [1, 2])               -- Structural equality, independent of allocation identity
assert(.{ x: 1, y: 2 } == .{ y: 2, x: 1 })
let nan = 0.0 / 0.0
assert(!(nan == nan) && nan != nan)
let mut ordered: [str: int] = ["b": 1, "a": 2]
ordered !> Map::set("b", 3)
assert(Map::keys(ordered) == ["b", "a"]) -- Replacing a value preserves its key's position
-- let bad_keys: [f64: int] = [nan: 1] -- Error [E0301]: floating-point keys are not admitted
-- let graph_key = [.{ id: 1 }: 0]    -- Error [E0301]: immutable records are still reference-type keys
```

`!=` negates `==`. Equality requires compatible same-typed values (`E0301` otherwise), except the Option/None tag test below.

| Values | Equality |
| :--- | :--- |
| Numbers | Same numeric type; IEEE NaN unequal to everything, signed zeros equal |
| `bool`, `str`, `bytes`, `()` | Value, exact Unicode scalar sequence, byte sequence, unit |
| Records / tuples / arrays | Labels and values / positions and values / length and elements |
| Sums / nominal wrappers | Constructor and payload / same nominal identity and underlying value (`E0305` for distinct wrappers) |
| Maps / sets | Key-value membership / membership; insertion order ignored |
| Ordinary opaque types | Same-type equality when the representation supports it |
| Option compared to `None` | Tag only; payload need not support equality |
| Callable, task, resource, type-function values | `E0301`, including nested constituents |

Ordering (`<`, `<=`, `>`, `>=`) accepts same-typed numbers, strings, or bytes only (`E0301`). Strings/bytes use lexicographic order; every ordered comparison involving NaN is false.

For finite cyclic graphs, equality is the greatest binary relation satisfying these structural rules; allocation identity and sharing count are irrelevant. Comparison terminates without user code or overlapping writes; provenance and exclusivity still govern reads.

| Map key / set element type | Eligibility |
| :--- | :--- |
| `bool`, integers including `bigint`, `str`, `bytes`, `()` | Allowed |
| Nominal / ordinary opaque wrappers | Allowed when recursively preserving one of those value representations |
| Floats, reference graphs (even Immut), callables, resources | `E0301` |

Eligibility depends on the concrete type, not equality support alone. Keys are copied by value: source reassignment cannot change them. No freezing, graph cloning, or user equality/order/hash callbacks occur.

| Collection operation | Order |
| :--- | :--- |
| Array iteration | Increasing index |
| Map/set iteration; `Map::keys`/`values` | First insertion |
| Replace map value / reinsert present set member | Keep position |
| Remove, then insert | Append |
| Duplicate map literal key | Last value, first position; operands still evaluate left-to-right |
| Set `union` | Left order, then new right members |
| Set `intersect` / `diff` | Left order |

### Logical Operators

`&&` and `||` exhibit strict short-circuiting: the right operand is evaluated only when the left operand does not determine the result.

```ril
let valid_and = (p != None) && (p.x > 0) -- Right side not evaluated if p == None
let valid_or  = (len(items) == 0) || (items[0] > 0) -- Right side not evaluated if items is empty
let negated   = !valid_and             -- Unary logical NOT
```

### Range and Slicing Expressions

```ril
let r1 = 0..5                          -- Half-open range [0, 5)
let r2 = 0..=5                         -- Closed range [0, 5]

let arr = [10, 20, 30, 40, 50]
let slice = arr[1..4]                  -- [20, 30, 40]
let prefix = arr[..3]                  -- [10, 20, 30]
let suffix = arr[2..]                  -- [30, 40, 50]
let empty = arr[len(arr)..len(arr)]   -- OK: empty window at the end
-- arr[2..1]                          -- Panics: reversed half-open bounds
-- arr[-1..2]                         -- Panics: negative lower bound
-- arr[0..=len(arr)]                  -- Panics: a written inclusive upper bound must index an element
```

```ril
let mut source = [1, 2, 3]
let view window = source[0..2]
source[0] = 9
-- window[0] = 4                      -- Error [E0520]: slice windows grant no writes
-- source !> Array::push(4)           -- Error [E0537]: changes storage structure before window's later use
assert(window[0] == 9 && len(window) == 2)
source !> Array::push(4)              -- OK: no remaining use of this window or an alias
```

- **Window Identity**: Slicing an array of elements T yields shape `[]T`. It evaluates its source and bounds once and creates a read-only window over the selected element slots; it does not copy those slots. The range and window length remain fixed. Immutable sources yield immutable windows; live sources retain their pinned origins and require a live-compatible binding. Live `var`/`var mut` origins remain inadmissible (`E0531`).
- **Bounds**: For length N, a half-open window requires `0 <= lower <= upper <= N`; equal bounds produce an empty window, including at N. Omitted lower bounds mean zero; an omitted upper bound denotes the exclusive end N, with either range spelling. A written inclusive upper bound h requires `0 <= lower <= h < N` and selects through h. Negative, reversed, or out-of-range bounds panic; bounds are never clamped.
- **Observation**: Replacing or exchanging existing element values is visible through the window, subject to ordinary exclusivity. A separately projected child reference keeps the object obtained at projection time, as for other views. The window never supplies mutable authority; use explicit `clone` for independent writable data.
- **Structural Stability (`E0537`)**: While the window or any of its aliases may still be used on a statically possible path, reject a structural change to the same backing collection, including append, insert, removal, and truncation. Calls, captured windows, and returned windows preserve this obligation. It ends only after all possible uses end; a source-level alias or guessed execution order is not proof. Same-length element replacement is not a structural change.

### Pipeline Operators

- **Linear Pipeline (`|>`)**: Passes the left expression as the first argument to the right callable: `x |> f` desugars to `f(x)`.
- **Mutating Pipeline (`!>`)**: Passes the mutable left lvalue to the right mutating callable: `x !> f` desugars to `f(mut x)`. It never supplies `^mut` implicitly.
- **Call Form and Propagation**: `x |> f(a)` means `f(x, a)`; `x !> f(a)` means `f(mut x, a)`. The left operand evaluates first, then the written right arguments. Trailing closures supply the final argument. Postfix `?` keeps its ordinary precedence: use `(x !> f(a))?` to propagate the whole pipeline result.

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
-- let bad_top_record = find_record(1)? -- Error [E0205]: QuestionMarkOutsideFunctionError: postfix '?' operator used outside function or closure body; no enclosing activation frame to receive early return

let opt: ?int = None
let v1 = opt ?? 100                    -- 100 (Option fallback with default value)
let v2 = opt ?? compute_default()       -- Evaluates compute_default only when opt is None
let optional_action: ?(fn() -> int) = None
let action = optional_action ?? (\-> 7) -- The fallback is a function value, not an invocation
assert(action() == 7)

let res: Result<int, str> = Err("unavailable")
let recovered = res ?? \err -> 0       -- 0: Result fallback MUST consume the error
-- let bad = res ?? 0                  -- Error [E0711]: InvalidResultFallbackError: Result fallback requires closure '\err -> ...'
-- let illegal = opt ?? return 0       -- Error [E0710]: IllegalControlTransferInFallbackError: illegal control transfer inside fallback operator '??'

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
| `Option<T>?` | Unwrap T | Return `None`; enclosing callable must return `Option<U>` (`E0301`) |
| `Result<T, E>?` | Unwrap T | Return `Err(e)`; enclosing result must accept E (`E0301`) |
| `Option<T> ?? rhs` | Unwrap T; skip rhs | Evaluate rhs as T; never auto-invoke a supplier |
| `Result<T, E> ?? handler` | Unwrap T; skip handler | Evaluate and invoke `fn(E) -> T` once; raw T is `E0711` |

`?` outside a function/closure is `E0205`, including module initializers. It performs no Option/Result or error conversion; payload provenance, permissions, and nested inspection duties survive.

`??` evaluates its left operand once. Callback effects/permissions remain checked. Direct outward `return`/`last`/`next` is `E0710`; a return inside a nested callable stays local to it.

| Safe access | Rule |
| :--- | :--- |
| `?.` | Field projection from an optional receiver |
| `?[` | Array/slice/map element lookup, also through an optional receiver |
| `None` receiver | Return `None`; skip access and index evaluation |
| Missing key / out-of-bounds element | Return `None` |
| Selected U / selected `Option<U>` | `Some(value)` / unchanged Option; no further flattening |
| Range index | Use ordinary slicing syntax and bounds rules |

### Record Construction and Functional Update

Explicit fields override equally named fields from a value spread, independent of their written position. Multiple explicit definitions of one field, or unresolved conflicting spread sources without an explicit override, are `E0203`. A spread copies values and references with their existing permissions; it does not deep-clone live data or make it immutable.

```ril
type Point = { x: int, y: int, z: int }

let p1 = Point.{ x: 1, y: 2, z: 3 }
let p2 = Point.{ z: 10, ..p1 }         -- Functional record update: { x: 1, y: 2, z: 10 }
```

### Assignments and Compound Assignments

Assignments require an addressable mutable lvalue target. Assignments are expressions evaluating to `()`.

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
-- pinned_buf = Buffer.{ capacity: 64 } -- Error [E0502]: PinnedHandleReassignmentError: use 'var mut' when reassignment and interior writes are both needed

-- Chained assignment is prohibited:
-- x = y = 10                          -- Error [E0701]: ChainedAssignmentProhibitedError: assignment chaining is prohibited
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
    -- read_value()                    -- Error [E0204]: value is not initialized
    let value = 1
    read_value()                       -- OK
    where
        fn read_value() -> int &{closure, value} { value }
}
```

Local bindings become available after initialization. Hoisted helpers may capture later bindings, but invocation, publication, and passing to another call require every capture initialized (`E0204`). Hoisting executes neither initializers nor helpers.

```ril
-- Mutually recursive functions and types hoisted in block 'where':
let total = {
    let base = compute_base()
    let parity = is_even(base)
    base
where
    fn compute_base() -> int { 100 }
    fn is_even(n: int) -> bool @Div { if n == 0 { true } else { is_odd(n - 1) } }
    fn is_odd(n: int) -> bool @Div { if n == 0 { false } else { is_even(n - 1) } }
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
--     type Step = int                 -- Error [E0703]: IllegalSequentialDeclarationError: declarations of 'type' are prohibited in sequential statement stream; place in 'where' clause
--     eff Bail { exit() -> never }    -- Error [E0703]: IllegalSequentialDeclarationError: declarations of 'eff' are prohibited in sequential statement stream; place in 'where' clause
--     x + 1
-- }

-- Prohibited: Variable bindings declared in 'where' (E0702):
-- let bad_where = {
--     base + 1
-- where
--     let base = 10                   -- Error [E0702]: InvalidWhereItemError: variable bindings cannot be declared in 'where' clause
-- }

-- Prohibited: Undischarged local effect escaping block boundary (E0618):
-- fn bad_effect_leak() -> int @LocalStep { -- Error [E0618]: UndischargedLocalEffectError: local effect 'LocalStep' cannot escape enclosing block to function signature
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

`if` requires a boolean condition. Its branches must have compatible types; a `never` branch imposes no returned-value constraint. An `if` without an `else` evaluates to `()` and requires its then branch to have type `()` or `never` (`E0301` otherwise).

```ril
let max = if a > b { a } else { b }

if logging_enabled {
    println("log message")             -- Evaluates to ()
}

-- Incompatible branch types are statically rejected:
-- let bad = if true { 10 } else { "error" } -- Error [E0301]: TypeMismatchError: if-else branches have incompatible types: expected 'int', found 'str'
```

### Loop Expressions

```ebnf
LoopExpr  ::= "loop" Block
WhileExpr ::= "while" Expression Block
ForExpr   ::= "for" Expression "as" Pattern Block
```

```ril
-- 'loop' with 'last' yielding a value:
var i = 0
let found = loop {
    i += 1
    if i == 5 { next }                 -- OK: skips to next iteration via 'next'
    if i == 10 { last i * 2 }          -- Loop evaluates to 20 via 'last'
}

-- 'while' loop:
while i > 0 {
    i -= 1
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
| `while` | Boolean condition; result and `last` values are unit (`E0301`) |
| `for` | Result and `last` values are unit (`E0301`); element pattern irrefutable (`E0303`), never an implicit filter |
| `loop` | Common type of reachable `last` values, or `never` if none |

Body tails are discarded subject to Result inspection duties.

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
-- last 42                                  -- Error [E0707]: InvalidControlTransferContextError: 'last' statement used outside loop body
-- next                                     -- Error [E0707]: InvalidControlTransferContextError: 'next' statement used outside loop body
```

### Guarded Bindings and Non-Vacuous Invariant

`let Pattern = expr else { Block }` matches a refutable pattern or diverges.

```ril
fn unwrap_or_zero(value: ?int) -> int {
    -- let Some(x) = value             -- Error [E0303]: refutable binding needs else
    let Some(x) = value else { return 0 }
    x
}
```

Without `else`, patterns must be irrefutable under the initializer's static type/refinement (`E0303`), including mutable/destructuring bindings. A single-variant constructor may qualify. Guarded names exist after success, not in the failure block.

- **Divergence Invariant**: The `else` block MUST diverge (evaluate to `never`).
- **Universal Non-Vacuous Binding Invariant (`E0309`)**: All `let` statements (both simple `let Pattern = expr` and guarded `let Pattern = expr else { ... }`) MUST bind at least one variable into the enclosing lexical scope, with the sole exception of the explicit wildcard discard pattern `let _ = expr`. Patterns that introduce zero variable bindings (such as `let Marker = m`, `let () = expr`, `let Ok() = expr else { ... }`, `let None = expr else { ... }`, or `let _ = expr else { ... }`) are statically rejected (`E0309: VacuousBindingError`). To conditionally guard or test without binding variables, developers must use postfix `?`, boolean pattern tests (`if expr is Pattern`), or explicit `match` expressions.

```ril
fn process_account(data: [str: str]) -> Result<str, str> {
    -- The 'else' block MUST diverge (evaluate to 'never') and MUST bind >= 1 variable:
    let Some(id) = data["account_id"] else {
        return Err("missing account_id") -- OK: diverges via 'return', binds variable 'id'
    }

    -- Non-diverging 'else' is statically rejected:
    -- let Some(name) = data["name"] else {
    --     println("name missing")     -- Error [E0321]: NonDivergentElseError: 'else' branch of 'let ... else' must diverge
    -- }

    -- Prohibited: Vacuous guarded binding without variable bindings:
    -- let Ok() = save_profile(id) else {
    --     return Err("save failed")   -- Error [E0309]: VacuousBindingError: 'let ... else' pattern must bind at least one variable; use postfix '?' or 'if expr is ...' instead
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
                     | TuplePattern | RecordPattern | ConstructorPattern | RangePattern
BindingModifier    ::= "mut" | "var" [ "mut" ]
VariablePattern    ::= [ BindingModifier ] Identifier
ConstructorPattern ::= QualifiedName [ "(" [ PatternList ] ")" ]
PatternList        ::= Pattern { "," Pattern } [ "," ]
TuplePattern       ::= "(" Pattern "," Pattern { "," Pattern } [ "," ] ")" | "(" ")"
RecordPattern      ::= [ TypeReference ] ".{" [ RecordPatternField { "," RecordPatternField } [ "," ] ] "}"
RecordPatternField ::= [ BindingModifier ] FieldLabel [ ":" Pattern ] | ".." Identifier
```

Matches are evaluated top-to-bottom and must be exhaustive. A trailing guard belongs to the whole or-pattern, not just its last alternative. Every alternative binds the same identifiers with compatible types and modes; a guard cannot establish exhaustiveness.

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
--     }                               -- Error [E0303]: NonExhaustiveMatchError: non-exhaustive match expression, missing variant 'Point'
-- }
```

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
--     }                               -- Error [E0303]: NonExhaustiveMatchError: non-exhaustive match: pattern guards do not prove coverage of all inputs
-- }

-- Boolean pattern test via 'is':
let is_origin = s is Shape::Point
let is_large_circle = s is Shape::Circle(r) if r > 100.0

-- Constructor and tuple pattern destructuring (Constructor-Tuple Equivalence):
let result_pair: Result<(int, str), str> = Ok(200, "OK")
match result_pair {
    Ok(code, msg) -> println(msg),       -- OK: positional tuple unpack (n = 2)
    -- Ok(p) -> println(p.1),            -- Error [E0304]: preceding arm covers every Ok
    -- Ok((code, msg)) -> println(msg),  -- Error [E0304]: equivalent pattern is unreachable here
    -- Ok(a, b, c) -> println(a),        -- Error [E0314]: ArityMismatchError: arity mismatch: variant 'Ok' payload expects 2 elements of type (int, str), found 3
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
NarrowingPredicate ::= NarrowingTarget "is" QualifiedName
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
- **Zero-Binding Refinement**: Narrowing refines existing bindings in-place across conditional branches without introducing new variable bindings (contrasting with `match` and `let ... else` which introduce new bindings).
- **Non-Binding Predicates**: Pattern variables in `x is Variant(p)` are scoped strictly to trailing guards (`if guard`) and cannot escape to branch blocks (`E0204`).
- **Payload Projection ($S|_V$)**: Testing `x is V` refines sum type $S$ to variant $S|_V$ ([Sum Types and GADTs](#sum-types-and-gadts)):
   - $n = 0$: No payload; projection raises `E0301`.
   - $n = 1$: Projected via `.0` (`p.0`). `?T != None` directly unboxes to `T`.
   - $n \ge 2$: Projected via positional tuple indices `.0`, `.1`, ..., `.(n-1)`.
   - Record: Projected via declared field names (`x.field`).
- **Stability & Invalidation**:
   - `let`: Permanently narrowed across dominance region.
   - `var` / `var mut`: Slot assignment, including compound assignment, invalidates that slot's narrowing (`E0310`). Interior writes through `var mut`, including `!>` calls, invalidate overlapping facts according to their actual write origins; `!>` does not reassign the slot.
   - `let mut`: Tag identity is pinned (`E0502`); `mut` fields invalidate upon write.
- **Transitive Latent Havoc**: Invoking a callable whose effective writes reach v, through a global or captured group, a contract reference, a callback, or an active handler, resets the affected refinement to $T_{\text{root}}$. Group spelling does not change the actual write origin.
- **Anti-Aliasing (`E0533`)**: Narrowing an unstable live origin whose overlapping writers can act during the refinement is rejected (`E0533`). Views do not make mutable data stable. A known write invalidates affected facts (`E0310`). Copy a scalar or use an independent immutable snapshot to obtain stable refinement.
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
        -- let bad = opt + 2                   -- Error [E0310]: InvalidatedNarrowingAccessError: variable 'opt' was narrowed to 'int', but refinement was invalidated by reassignment; current flow type is '?int'
    }
}

-- Contradictory narrowing rejection (E0311):
fn test_contradiction(g: Geometry) {
    if g is Geometry::Circle {
        -- if g is Geometry::Rect {            -- Error [E0311]: ContradictoryNarrowingError: condition 'g is Geometry::Rect' is statically unsatisfiable; target is already narrowed to 'Geometry::Circle'
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

-- Pattern bindings in 'is' cannot escape guard clause:
fn test_non_binding_predicate(g: Geometry) {
    if g is Geometry::Circle(r) if r > 5.0 {
        let radius = g.0                       -- OK: payload access via .0
        -- let escaped = r                     -- Error [E0204]: UnresolvedIdentifierError: unresolved identifier 'r'; pattern bindings in 'is' are strictly scoped to guard clause
    }
}

-- Transitive Latent Havoc via mutating call:
fn test_latent_havoc() {
    var count: ?int = Some(10)
    if count != None {
        let mut step = \-> &{closure, mut count} { count = None }
        step()                                 -- Mutating call invalidates 'count'
        -- let bad_use = count + 1             -- Error [E0310]: InvalidatedNarrowingAccessError: variable 'count' was narrowed to 'int', but refinement was invalidated by mutating call 'step()'; current flow type is '?int'
    }
}

-- Generic confinement: bare type parameter rejected:
fn test_generic_confinement<T>(x: Geometry) {
    -- if x is T {                             -- Error [E0301]: TypeMismatchError: cannot test unconstrained generic type parameter 'T' in narrowing predicate
    --     println("invalid")
    -- }
}

-- Dead-path mutation phase ordering:
fn test_dead_write_phase_ordering() {
    -- var unused: ?int = Some(10)            -- Error [E0527]: UnusedMutableBindingError: variable 'unused' declared 'var' is never modified along reachable paths
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
```

At an ordinary call, a leading `mut`/`^mut` is an argument mode and still requires an assignable target. The general expression production does not admit `f(^mut clone(x))` as a substitute: bind a writable result first. A parenthesized sharing expression is an ordinary read-only argument, cannot satisfy a mutable formal, and cannot authorize that formal to retain a writer. Constructor storage follows the aggregate sharing rules.

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
--     fn helper(n: int) -> int { n * 2 }    -- Error [E0704]: InvalidSignatureWhereItemError: 'fn' cannot be declared in signature 'where' clause; place in block 'where' clause
--     eff Yield { emit(int) -> () }         -- Error [E0704]: InvalidSignatureWhereItemError: 'eff' cannot be declared in signature 'where' clause; place in block 'where' clause
-- {
--     helper(x)
-- }

-- Prohibited: Downward reference from waist to block where (E0705):
-- fn bad_downward<T>(item: T) -> Wrapper
-- where
--     type Wrapper = { state: InternalState } -- Error [E0705]: DownwardScopeReferenceError: signature 'where' clause cannot reference 'InternalState' declared in inner block 'where' clause
-- {
--     Wrapper.{ state: .{ code: 0 } }
-- where
--     type InternalState = { code: int }
-- }

-- Prohibited: Signature referencing type defined in block where (E0706):
-- fn bad_sig_target(cb: Callback) -> ()      -- Error [E0706]: SignatureTypeNotInWaistWhereError: type 'Callback' used in function signature must be declared in signature 'where' clause, not block 'where' clause
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
--     type Handler = fn(int) -> ()           -- Error [E0203]: DuplicateDeclarationError: type 'Handler' is already declared in signature 'where' clause
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

### Default Purity and Callback Dependencies

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

| Annotation context | Omitted row | Explicit empty row |
| :--- | :--- | :--- |
| Named definition without callback-dependent obligations | No concrete outward obligations in that domain | The same zero requirement |
| Named definition with symbolic callback dependencies | No undeclared concrete obligations; retain the symbolic dependencies | Constrain the total row, including those dependencies, to zero |
| Callable type | Preserve the actual value's inferred obligations | Require zero total residual obligations |
| Anonymous definition | Infer and verify its actual obligations | Constrain the total residual obligations to zero |

`&{}` closes the whole state domain, including captures and inherited obligations; it is not an empty global-only group. `@{}` closes the whole residual-effect domain. Neither row erases latent obligations of a returned callable or grants permission to create an otherwise prohibited environment.

### Parameter Modes, Caller Obligations, and Defaults

```ril
type Cell = { mut count: int }
fn bump(mut cell: Cell) &mut { cell.count += 1 }
let mut cell = Cell.{ count: 0 }
bump(mut cell)
cell !> bump()
-- bump(cell)                          -- Error [E0520]: explicit mutable argument required
let view observed = cell
-- bump(mut observed)                  -- Error [E0520]: view has no write permission
```

| Parameter mode | Caller form | Authority |
| :--- | :--- | :--- |
| `p: T` | `expression` | Read-only access; preserves immutable/live origin facts |
| `mut p: T` | `mut target` | Temporary interior/environment write access; no retained writable path after the call |
| `^mut p: T` | `^mut target` | Write access plus permission to retain a writable path beyond the call |

- Mutable parameters require reference data or a mutable callable environment (`E0401`), remain pinned (`E0502`), and cannot use `var` (`E0403`).
- Annotations, forwarding, and subtyping do not infer parameter modes. Retention requires `^mut` and its capability (`E0510`); `!>` supplies only `mut`.

A callback's parameter list and the mode of the callback handle are distinct. `f: fn(mut T) -> R` is a read-only function handle accepting a mutable *data argument*. `mut f: fn(T) -> R` grants permission to invoke a mutable *captured environment*. Both can be required by the same function. Mutable inline closures must first be bound to an appropriate writable handle before being passed with `mut`.

#### Default Parameters and Named Arguments

- Defaults have no residual effects or state obligations. Mutable parameters cannot have defaults (`E0404`).
- Explicit arguments evaluate in written left-to-right order; omitted defaults follow in parameter order. A default may use earlier parameters, not itself or later parameters.
- Named arguments bind by parameter name. Supplying one parameter twice is `E0325`.
- Function generic defaults are prohibited (`E0317`).

```ril
fn create_server(host: str, port: int = 8080, enable_tls: bool = true) -> str {
    "{host}:{port} (tls={enable_tls})"
}
let address = create_server("localhost", enable_tls: false)
-- create_server("localhost", host: "duplicate") -- Error [E0325]: duplicate argument
```

### Anonymous Functions, Trailing Closures, and Projection Accessors

```ebnf
AnonFnExpr    ::= "\" [ AnonParams ] "->" [ EffectAnnot ] [ StateAnnot ] ( Expression | Block )
AnonParams    ::= AnonParam { "," AnonParam } [ "," ]
AnonParam     ::= [ ParameterMode ] Identifier [ ":" TypeExpression ]
AccessorExpr  ::= "\" AccessorNav AccessorField { AccessorNav AccessorField }
AccessorNav   ::= "." | "?."
AccessorField ::= Identifier | TupleIndex
(* TupleIndex is defined in its earlier grammar production. *)
```

- **Unary Desugaring Equivalence**: An `AccessorExpr` evaluates to a unary pure function projecting properties from its argument:
   - `\.field` desugars to `\x -> x.field`
   - `\.0` desugars to `\x -> x.0`
   - `\.field?.subfield` desugars to `\x -> x.field?.subfield`
   - `\?.field` desugars to `\x -> x?.field`
- **Product Type Duality**:
   - `Identifier` statically projects named fields from records (`{...}`), nominal wrappers, or refined named variants. Unknown fields trigger `E0307`.
   - `TupleIndex` statically projects 0-indexed positional components from tuples (`(T0, T1, ...)`) or refined positional variant payloads ($S|_V$). Positional indices are statically checked at compile time against tuple arity $n$ ($0 \le i < n$). Out-of-bounds indices trigger `E0312`.
- **Safe Navigation Propagation**:
   - If any navigation segment uses safe navigation `?.`, evaluation short-circuits to `None` when the intermediate receiver is `None`. The resulting accessor closure return type is automatically lifted into `?T`.
- **Collection Segregation**:
   - Collections (slices `[]T`, maps `[K: V]`, and prelude `Set<T>`) are not product types and cannot be projected via dot/accessor syntax directly (`E0301`). Element and key extractions require explicit bracket indexing (`\arr -> arr?[i]`) or higher-order combinators (`Array::first`, `Map::get`).

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
-- let bad_idx = pairs |> Array::map(\.2)                     -- Error [E0312]: TupleIndexOutOfBoundsError: tuple index 2 out of bounds for (int, str)
-- let bad_field = employees |> Array::map(\.age)             -- Error [E0307]: MissingFieldError: unknown field 'age' on type 'Employee'
-- let bad_arr = [[1, 2], [3]] |> Array::map(\.0)             -- Error [E0301]: TypeMismatchError: collections do not have named fields or static tuple projections
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

- **Abstraction**: `&closure` abbreviates environment obligations. Actual origins, modes, sharing hazards, and effects survive type abstraction, branching, storage, and return.
- **Definitions (`E0534`)**: A named definition states concrete invocation obligations under the default-purity rules. Direct capture access uses the appropriate source group, not a standalone `&closure` abbreviation. Parameter/return callable types may use that abbreviation. Anonymous captures are inferred; explicit annotations remain checked and cannot hide them.
- **Creation**: New environments surviving the enclosing callable's return require `&capture`, including those nested in returned aggregates. Forwarding existing environments or using call-local ones does not.
- Anonymous functions capture free value bindings, including module bindings. Module-level named functions use declared external access; escaping block-local functions retain their required lexical environments.
- **Binding Choice**: A immutable environment can be bound with `let`. An environment that only observes live pinned roots can be bound with `let view`. A persistent mutable environment requires a writable handle. These are environment facts, not consequences of the visible `&closure` spelling.
- **Sharing**: A private cell exposed only through one new closure requires `&capture`. Exposing another authority to that cell also requires `&^mut`.

### Higher-Order Functions and Capability Forwarding

```ril
fn apply<T, R>(value: T, f: fn(T) -> R) -> R { f(value) }
eff Logger { log(str) -> () }
fn logged_square(n: int) -> int @Logger {
    Logger::log("calculating")
    n * n
}
fn caller() -> int @Logger { apply(5, logged_square) }

fn invoke_mut(mut f: fn() -> int &closure) -> int &mut { f() }
let mut counter = create_counter(0)
let first = invoke_mut(mut counter)    -- Explicit callback-handle authority
-- apply(0, \mut target -> target)    -- Error [E0301]: callback parameter modes do not match
```

Higher-order calls forward actual effect and state obligations without changing permissions or parameter modes. Omitted callable rows preserve these dependencies separately for each actual argument. Only still-symbolic callable-parameter dependencies may remain implicit in a named definition; concrete invocation obligations require declaration after local discharge. An explicit closed row constrains the admitted arguments, as specified under [Callable Signature Abstraction](#callable-signature-abstraction).

```ril
fn apply_to_cell(mut cell: Cell, f: fn(mut Cell) -> () &mut) &mut {
    f(mut cell)
}
let mut cell = Cell.{ count: 0 }
apply_to_cell(mut cell, bump)           -- Both declaration and call specify the data mode
```

`Array::map`, `filter`, and `fold` explicitly support ordinary and `mut callback` forms. Only the latter grants mutable-environment invocation. This is call-site mode selection, not implicit conversion; parallel contracts add confinement checks.

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
-- fn bad_clear(mut list: []int) {     -- Error [E0510]: MissingCapabilityAnnotationError: mutating operation requires caller signature to declare '&mut'
--     list !> Array::truncate(0)
-- }
```

### Retained Mutable Sharing

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
- **No Duplicate Boundary Spelling**: Receiving an authority already produced under a checked callable retention contract does not require another local marker. Callable return/tail expressions, inferred lexical captures, and handler environments keep their existing rules; no new return or capture syntax is required. A plain block is not a callable retention boundary. Aliasing an already created mutable closure locally still requires the marker. A `clone` source/copy isolation contract does not itself mark the copy's possible internal writable aliases.
- **Confinement**: Local `^mut` does not by itself add external `&^mut` to the enclosing function. Conversely, local discharge does not remove required markers at local data-sharing sites. Captured and returned sharing still contributes its actual authority roots whether or not its facts are written explicitly.

```ril
fn retain(^mut cell: Cell) -> Cell &^mut { cell }
let mut original = Cell.{ count: 0 }
let mut returned = retain(^mut original) -- Retention already marked at the call boundary
returned.count += 1
original.count += 1
-- let mut hidden = retain(original)  -- Error [E0520]: ordinary argument cannot provide retention authority
-- let mut hidden = retain((^mut original)) -- Error [E0520]: expression is not a ^mut argument mode
-- let mut hidden = retain(^mut clone(original)) -- Error [E0520]: mutable argument must be an assignable target
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

`Array::push` and `Map::set` preserve a normal argument's read-only permission. Their explicit `^mut value` form retains write permission and incurs `&^mut`. A writable container never upgrades an immutable/view element (`E0522`).

### External State Tracking

Accessing module-level or captured bindings requires the corresponding named source group. A named definition must also declare concrete named obligations inherited from calls, either with a matching source group or an admissible function state contract reference. Only genuine callable-parameter dependencies retain implicit symbolic forwarding.

Within either kind of source group, a bare item permits read-only access, whether its actual data is immutable or live. It does not promise deep immutability or create a `let view` binding. `mut name` adds writes; `^mut name` additionally permits retained writable sharing. Each mode applies only to its own item.

Direct access includes storage access in the named definition's lexical anonymous functions and handler arms when those operations contribute to its current invocation, and mutable argument permissions it supplies. Direct access requires its own declarations after local discharge; a contract reference cannot replace them. Referencing a named function declaration is not itself a read of storage; accessing a stored external callback is. Future operations of a returned callable remain latent, while its creation, capture, and retention obligations are checked separately.

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
-- fn bad_read() -> str { APP_CONFIG_NAME }          -- Error [E0510]: MissingCapabilityAnnotationError: accessing external state requires caller signature to declare capability '&{APP_CONFIG_NAME}'
-- fn bad_write() { transaction_count += 1 }        -- Error [E0510]: MissingCapabilityAnnotationError: mutating external state requires caller signature to declare capability '&{mut transaction_count}'

-- Prohibition of Anonymous Concealment:
-- fn conceal_write() &mut { transaction_count += 1 } -- Error [E0510]: MissingCapabilityAnnotationError: cannot use anonymous '&mut' to conceal external state 'transaction_count'
```

```ril
-- Uses record_transaction and transaction_count from the preceding declarations.
fn direct_call() &{mut transaction_count} { record_transaction() }
fn alias_call() &{mut transaction_count} {
    let action = record_transaction
    action()
}
fn invoke_action(action: fn() -> ()) { action() }
fn parameter_call() &{mut transaction_count} { invoke_action(record_transaction) }
-- All three concrete wrappers must declare the inherited access.
-- fn hidden_call() { record_transaction() } -- Error [E0510]: omission is not permission to inherit concrete state
-- fn hidden_write() { transaction_count += 1 } -- Error [E0510]: this is direct storage access
-- fn falsely_closed() &{} { alias_call() }     -- Error [E0534]: inferred callee state is not empty
```

### State Groups and Captured Layers

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

-- closure is an ordinary module variable, not a reserved identifier:
var closure = 0
var x = 0
fn bump_names() &{mut closure, mut x} { closure += 1; x += 1 }
fn read_closure() -> int &{closure} { closure }
fn read_both() -> int &{x, closure} { x + closure }
-- &{closure, x} is always a capture group; it cannot denote these two global reads.
-- &{closure,} is Error [E0538]: a captured group requires a real item.
```

Standalone `&capture`, `&mut`, `&^mut`, and the callable-type abstraction `&closure` are not group entries. `&{}` is the total empty-state constraint, not an empty global group. No group declares that storage is unique, consumes authority, or merges a retained handler definition; those obligations retain their existing checks.

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

- **Provider and Position (`E0539`)**: `&callee` or `&Module::callee` references the verified concrete named-state contract of a visible ordinary named Ril function definition. Ordinary name resolution and visibility apply first (`E0204`/`E0201`); after successful resolution, a wrong provider kind or annotation position is `E0539`. This form is allowed only in the state annotation of an ordinary named function definition. It is not permitted in callable types, anonymous-function annotations, effect operation declarations, or bodyless foreign declarations. A value alias or callable parameter is not a provider declaration.
- **Concrete Named Projection**: A reference denotes the provider's concrete global/captured source items and their verified access modes for its current invocation, including concrete named dependencies obtained through other calls. The bindings and lexical owners remain anchored to the provider's scope. It does not include effects, anonymous parameter permissions, standalone `&capture`/`&^mut`, symbolic callback dependencies, or a returned callable's future invocation obligations.
- **Coverage, Not Authority**: The reference can cover matching concrete named obligations inherited from calls in the referencing definition. Apply the caller's existing local-discharge and parameter-authority rules before matching; a named source in the provider cannot substitute for the caller's required `&mut` or `&^mut`. The reference cannot cover the caller's direct storage access, including direct access in its handlers. Matching uses actual origin and permission relations, not just source names or a requirement that the body invoke one particular function name. Unrelated references do not cover an obligation (`E0510`); an unnecessary concrete reference remains subject to `E0529`.
- **No Erasure**: Calling through an alias or higher-order helper preserves the concrete dependencies. A provider reference cannot turn them into unknown callback dependencies, discharge a conflicting loan, or prove a recursive dependency empty. `&{}` continues to constrain the total state, including referenced state.
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
-- fn closed() &{} { advance() }     -- Error [E0534]: a closed definition cannot inherit this state
```

```ril
-- Counter is the ordinary module defined above.
use counter
-- fn private_reference() &Counter::private_advance {} -- Error [E0201]: private provider
-- fn unknown_reference() &Counter::missing {}         -- Error [E0204]: no such declaration
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

Permissions on an existing reference can be preserved or reduced, never upgraded by rebinding, wrapping, projection, abstraction, or return. Immutability is a separate guarantee; a live read-only view is not immutable. Deep clone and confined derive have their explicit fresh-data contracts.

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

Effective permissions on a projection, index, destructured reference, or returned path are limited by every reference handle in that access path as well as the stored constituent's permissions. A field's lack of slot-replacement permission does not itself reduce its child reference's permission. Plain `var`, views, and ordinary read-only parameters restrict all data and environment paths reached through them. This does not freeze the object or revoke an independent writer. An immutable function value's separately checked named external-state obligations remain callable obligations, not writes through its data handle.

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

### Callable Signature Abstraction

```ril
type Action = fn() -> ()               -- Omitted rows preserve actual obligations
type ClosedAction = fn() -> () @{} &{} -- Explicitly closed effect and capability rows
eff Log { write(str) -> () }
fn write_log() @Log { Log::write("event") }
let action: Action = write_log         -- OK: @Log remains required on invocation
-- let closed: ClosedAction = write_log -- Error [E0534]: explicit closed contract rejects @Log
```

- **Omission**: Callable types infer omitted rows and preserve actual effects, environment modes, named origins, and sharing obligations through every use.
- **Closed Rows**: `@{}` and `&{}` require zero residual effects and capabilities. Nonempty rows in callable types are total upper bounds; definition annotations follow the separate rules below. `&closure` abstracts capture details, but cannot erase an invocation's actual retained-publication obligation (`&^mut`, `E0534`). Already shared storage remains tracked even when invoking the callable creates no additional authority and therefore needs no new `&^mut`.
- **Definitions**: All named functions declare their concrete state and unhandled effect obligations, including known obligations inherited from callees. They may infer and forward only still-symbolic callable-parameter dependencies. Anonymous definitions may infer their actual obligations. Bodyless foreign declarations have closed omitted rows. Concrete minimal annotations and callable upper bounds are separate checks.
- **Handle Modes**: An abstract callable's inferred environment mode still controls binding and invocation. A mutable environment cannot become immutable or read-only-callable by changing its type annotation.
- **Inference Is Mandatory**: Returns, call sites, and symbolic higher-order forwarding need no additional surface annotation. Their complete origin and obligation facts remain available for [provenance diagnostics](#complete-provenance-and-optional-annotations), including through private callable abstractions. A named definition's default-purity obligations are still enforced; neither diagnostic visibility nor a user's inspection substitutes for those checks.

```ril
type Action = fn() -> ()
type ClosedAction = fn() -> () @{} &{}
eff Log { write(str) -> () }
fn plain() {}
fn logged() @Log { Log::write("event") }
fn invoke(action: Action) { action() }
fn closed(action: Action) @{} &{} { action() }

closed(plain)                         -- OK: the closed body constrains the admitted callback
-- closed(logged)                    -- Error [E0534]: argument violates the inferred closed callback constraint
let selected: Action = if choose_log { plain } else { logged } -- choose_log is a run-time bool input
-- let erased: ClosedAction = selected -- Error [E0534]: run-time choice retains the possible Log obligation
fn call_plain() { invoke(plain) }      -- OK: another Action value does not acquire logged's effects
fn call_logged() @Log { invoke(logged) }
-- fn missing_log() { let action = logged; invoke(action) }
-- Error [E0612]: a known effect does not become an unconstrained dependency through aliasing
```

- **Value-Specific Dependencies**: Omitted rows belong to each actual callable value and its uses, not one shared row attached to a type alias name. Callable values supplied through formal parameters, including their callable constituents, retain symbolic dependencies; actual arguments determine those dependencies at each use. A branch containing different callables retains every possible obligation. Such facts and constraints cross module boundaries with the callable's semantics even when private names cannot be written by the caller.
- **Definition Constraints**: An explicit empty row on a definition constrains that domain's total effective obligations, including forwarded obligations. It constrains admitted callable arguments where their omitted rows are inferable; the definition above is valid, but a violating argument is `E0534`. A fixed incompatible body is rejected at its definition. A callable type's explicit nonempty row is a total upper bound. A definition's nonempty annotations declare its concrete obligations; still-symbolic callback dependencies continue to be forwarded in addition to them. This does not close those dependencies implicitly.
- **Concrete Obligations**: Current-invocation state and unhandled effects that no longer depend on a callable parameter require the enclosing named function's declarations (`E0510`/`E0612`). Latent body operations of a returned or stored callable belong to its future invocation; current creation and sharing obligations remain separate. Moving a known callee through an alias, aggregate, or higher-order helper does not make its obligations unknown. Named source groups or admissible state contract references may cover inherited named state; direct storage access requires its own group.

```ril
-- Action, plain, and logged have the preceding contracts.
fn repeat(n: int, action: Action) @Div {
    if n > 0 { action(); repeat(n - 1, action) }
}
fn repeat_plain() @Div { repeat(2, plain) }
fn repeat_logged() @Div + Log { repeat(2, logged) }
-- fn erase_recursive() @Div { repeat(2, logged) }
-- Error [E0612]: recursion preserves the callback's Log dependency
```

The recursive edge does not discharge the callback dependency. Declaring the concrete `@Div` obligation does not restrict the callback to `@Div`; the effective instantiated effect row also contains its actual residual effects.

```ril
type StashingWorker = fn(^mut Entry) -> () &closure &^mut
type TemporaryWorker = fn(mut Entry) -> () &closure &mut
-- A value satisfying StashingWorker cannot be called as TemporaryWorker:
-- retained and temporary argument permissions are distinct contracts.
```

## Algebraic Effects and Concurrency

### Effect Declarations and Operation Signatures

Effects define abstract operation tags intercepted by enclosing handlers. An effect operation signature is an ordinary callable signature declaring argument types, return types, and optional state capabilities (`&mut`, `&^mut`):
- **Pure Operations**: Perform ambient control transfer without mutating caller storage.
- **Capability-Bearing Operations**: Operations that mutate caller storage explicitly declare state capabilities (`&mut`, `&^mut`), which callers and handlers must track and discharge under standard capability rules ([State and Capability Tracking](#state-and-capability-tracking)).

```ril
-- Pure Effect Operations & Ambient Context:
eff Console {
    print(str) -> (),
    read_line() -> str,
}

eff Context<T> {
    ask() -> T,                        -- OK: Ambient context value
}

-- Effect Operations Declaring Mutation Capabilities:
eff BufferIo {
    read_into(mut buf: []u8) -> int &mut, -- OK: Operation declares in-place buffer mutation
}

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

`with` covers the remaining block. `resume value` supplies the operation result and reinstalls this handler for the continuation; the arm itself uses outer handlers, even for its own family.

For block answer A, `resume value` and every arm's final value must have type A (`E0301`), including abort values and post-resumption tails.

```ebnf
WithStatement ::= "with" HandlerSpec
HandlerSpec   ::= "{" HandlerArm { "," HandlerArm } [ "," ] "}" | HandlerArm
HandlerArm    ::= QualifiedName "(" [ PatternList ] ")" "->" Expression
ResumeExpr    ::= "resume" Expression
```

```ril
eff ReadAt { get(int) -> int }
fn read_zero() -> int {
    with ReadAt::get(index) -> match index {
        0 -> resume 1,
        _ -> resume 2,
    }
    ReadAt::get(0)
}
-- with ReadAt::get(0) -> resume 1      -- Error [E0303]: handler parameter is refutable

type Cell = { mut count: int }
eff Edit { apply(mut Cell) -> () &mut }
fn edit_once(mut cell: Cell) -> int &mut {
    with Edit::apply(mut target) -> {
        target.count += 1
        let saved = target.count
        let answer = resume ()
        -- target.count += 1            -- Error [E0520]: this operation loan has ended
        answer + saved
    }
    Edit::apply(mut cell)
    cell.count
}
```

| Handler dispatch | Rule |
| :--- | :--- |
| One `with` | At most one arm per operation (`E0203`) |
| Parameters | Irrefutable patterns (`E0303`); mutable modes must match supplied authority |
| Request-value branches | Ordinary `if`/`match` inside the arm |
| Unlisted operation | Forward outward; retain unhandled effects (`E0612`) |
| Discharge an effect family | Cover every operation |

| Operation's ordinary `mut` loan | Arm's permission |
| :--- | :--- |
| Before `resume`, including evaluation of its value | Access through the matching parameter |
| Continuation starts | Return the loan; end all arm access through the parameter and derived aliases (`E0520`) |
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
type Deferred = fn() -> int @Read &{}
fn ask_read() -> int @Read { Read::get() }
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
}
-- fn incompatible() -> Deferred &capture {
--     with Read::get() -> resume 7
--     \-> Read::get()
-- }                                   -- Error [E0534]: the closed state row cannot erase the selected handler environment
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

### Affine Resumption and Delimited Early Abort

`resume` is affine: repeated use or escape from its arm is rejected. An arm returning without resumption aborts the delimited computation and runs scoped cleanup in reverse order. Prior writes remain committed.

```ril
-- Affine Resumption Violation: invoking resume more than once
eff Op { query() -> int }
fn bad_double_resume() -> int {
    with Op::query() -> {
        let first = resume 1
        -- let second = resume 2        -- Error [E0610]: DuplicateResumeInvocationError: affine resumption 'resume' invoked more than once
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

Ril provides the system operation families Fiber and Concurrent, the divergence obligation Div, and the alias Async:

- **`@Fiber` (Cooperative Fiber Control)**: Cooperative yielding and leaf I/O suspension without concurrent task branching authority. A leaf operation's contract determines what event completes its wait; there is no bare public park/unpark operation.
- **`@Concurrent` (Structured Concurrency)**: Structured scope, child-task forking, and joining, with the contracts below.
- **`@Async` (Suspendable I/O)**: An effect alias `{Fiber, Concurrent}` tracking uncolored asynchronous computations.
- **`@Div` (Divergence Tracking)**: Tracks potential non-termination in unbounded loops and general recursive functions. Total functions (`halt fn`) strictly prohibit `@Div`.

The sub-effect lattice satisfies:

$$\emptyset \subset \lbrace\text{Fiber}\rbrace \subset \lbrace\text{Fiber}, \text{Concurrent}\rbrace \equiv \text{Async}, \quad \text{disjoint from } \lbrace\text{Div}\rbrace$$

#### Normative Rules for Built-in System Effects
- **Least-Privilege Leaf I/O Principle (`@Fiber`)**: Leaf I/O operations requiring cooperative suspension without forking child tasks MUST declare only `@Fiber`. Holding `@Fiber` does not grant authority to fork concurrent tasks (`@Concurrent`), preserving frame containment and single-fiber DRF-SC invariants.
- **Compound Asynchronous Workflows (`@Async`)**: Functions that both suspend on I/O and manage concurrent child tasks declare `@Async`.
- **Scheduling and Value Generators**: `Fiber::yield() -> ()` yields cooperatively without emitting a user value. Value-emitting streams use user-defined effects such as `eff Yield<T> { emit(T) -> () }`, with affine resumption. A resumption cannot escape its handler arm to become a pull iterator (`E0611`).

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
    -- scope(\mut s -> {               -- Error [E0612]: UnhandledEffectError: function declares '@Fiber' but invokes unhandled '@Concurrent' primitive 'scope'
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
fn stream_remote_chunks(fd: int) -> () @Yield<[]u8> + Fiber + Div {
    while true {
        let chunk = read_socket_chunk(fd)
        if len(chunk) == 0 { last }
        Yield::emit(chunk)             -- Composes independent @Yield<[]u8> and @Fiber
    }
}

-- Divergence vs. Total Functions (@Div):
fn collatz(n: int) -> int @Div {
    if n <= 1 { 1 }
    else if n % 2 == 0 { collatz(n / 2) }
    else { collatz(3 * n + 1) }
}

-- Total function: provably terminates; @Div is strictly forbidden
halt fn factorial(n: int) -> int {
    if n <= 1 { 1 } else { n * factorial(n - 1) }
}
-- halt fn bad_total(n: int) -> int {  -- Error [E0820]: TotalityViolationError: 'halt fn' contains uncertified recursion or unbounded loop
--     collatz(n)
-- }
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

#### Normative Rules for Structured Concurrency

| Structured operation | Result |
| :--- | :--- |
| `s.fork(fn() -> T)` | `Task<T>` |
| `task.join()` | `Result<T, TaskFault>` |
| `scope(body)` where body returns `Result<T, TaskFault>` | Same result shape, after children terminate |

All three require `@Concurrent` and forward callback effects. No implicit join, result flattening, or conversion of business errors to panics occurs.
- **Receivers**: `s.fork` borrows its `mut s` receiver. `Task.join` uses result-observation authority, not mutable data access. Ordinary function arguments do not inherit these built-in contracts.
- **Lifetime (`E0606`)**: Children and their Scope/Task handles stay in their owning scope. Handles cannot be cloned, moved to another task, or hidden in escaping aggregates/closures.
- Join a result once. Task control state is external to its stable descriptor; ordinary returned data must satisfy immutable publication. Resources follow explicit transfer contracts.
- **Failure**: Child panic/double fault permanently fails the scope, even after inspection by `join`. Cancel unfinished descendants and active body waits. Any later `fork` cancels the body; returning `Ok` cannot restore success.
- **Cancellation**: Channel and leaf-I/O waits, pending joins, and nested scope waits must wake. Transfer to the scope boundary without resumption; user `with` cannot absorb cancellation.
- A join of the failed task may deliver its fault for inspection, without clearing failure. Other cancelled waits cannot complete successfully.
| Body exit | Before leaving |
| :--- | :--- |
| `Ok` | Wait for all children |
| `Err(TaskFault)`, panic, cancellation, or delimited abort | Cancel children and wait |

Run child cleanups except those abandoned by double fault. A parent panic/abort continues outward after the barrier; this scope does not catch it as a Result.
- **Termination**: The barrier forbids premature exit, not divergence. `@Div` remains an obligation and cannot be handled away. Built-in waits respond to cancellation; divergence outside cancellation points may prevent exit. No finite completion bound is promised.
- **Fault Order**: Among actual faults: double fault, then panic, then cancellation. Ties use task creation order, with an explicit body fault first. Cancellation never replaces its cause; different runs may produce different fault sets.
- **Confinement**: Share immutable ordinary data; reject live/mutable data and non-transferable resources (`E0601`). The listed resource exceptions are detached endpoint transfer and the limited immutable Sender clone-source borrow. Child system effects may include Fiber/Concurrent/Div; user effects need child-local handlers (`E0615`).
- **Transitive Access (`E0601`)**: Check every possible access through named external state, callees, callbacks, handlers, and cleanup. An immutable callable descriptor does not make its dependencies immutable. Outside live reads and ordinary writes are rejected even when no captured value crosses the boundary. Apply the separately listed resource permissions without extending them to ordinary data.
- **Results (`E0720`)**: `Task<Result<U, E>>` retains inner inspection duties. Normal success must inspect, propagate, or return them; join checks only the outer result. Abnormal unwinding may discard inaccessible/unfinished results, but cannot report success while losing an error.

```ril
-- Module declarations and an invocation fixture inside an owning scope:
type Cell = { mut count: int }
let SNAPSHOT = Cell.{ count: 1 }
let mut global_cell = Cell.{ count: 0 }
fn read_snapshot() -> int &{SNAPSHOT} { SNAPSHOT.count }
fn read_global() -> int &{global_cell} { global_cell.count }
fn write_global() &{mut global_cell} { global_cell.count += 1 }

let task = s.fork(read_snapshot)       -- OK: immutable named dependency
let result = task.join()
match result { Ok(value) -> { assert(value == 1) }, Err(_fault) -> {} }
-- s.fork(read_global)                -- Error [E0601]: outside live state, despite an immutable function value
-- s.fork(write_global)               -- Error [E0601]: outside write
-- s.fork(\-> read_global())          -- Error [E0601]: indirect access has the same origin
let selected = if choose_live { read_global } else { read_snapshot } -- run-time bool input
-- s.fork(selected)                   -- Error [E0601]: one possible dependency is live
```

```ril
pub type PanicInfo = { message: str, index: ?int }
pub type UnwindCause {
    Panicked(PanicInfo),
    EffectAborted,
    Cancelled,
}
pub type DoubleFaultInfo = { primary: UnwindCause, cleanup: PanicInfo }
pub type TaskFault {
    Panicked(PanicInfo),
    Cancelled,
    DoubleFaultFatal(DoubleFaultInfo),
}

fn inspect_business_result() -> Result<Result<int, str>, TaskFault> @Concurrent {
    scope \mut s -> {
        let task = s.fork(\-> {
            let answer: Result<int, str> = Err("domain failure")
            answer
        })
        let business = task.join()?
        Ok(business)                  -- The caller now owns the inner inspection obligation
    }
}
-- scope \mut s -> { s.fork(\-> Err("lost")); Ok() }
-- Error [E0720]: successful scope exit abandons a fallible task result
```


```ril
-- Returning s from a scope, or a closure capturing s, is E0606.
-- Returning a Task<T> handle rather than its joined data is E0606.
-- Capturing a let scoped resource into a returned callback is E0604.
-- Wrapping any such handle in a record does not change these outcomes.
```

### Deterministic Data Parallelism and Divide-and-Conquer Primitives

```ril
use ril/parallel
halt fn square_all(numbers: []f64) -> []f64 {
    numbers |> Parallel::map(\x -> x * x)
}
let first = [10, 20, 30, 40] |> Parallel::find(\x -> x > 25)
assert(first == Some(30))
```

#### The Colorless Parallel Principle and Domain Boundary

Parallel callbacks have no residual effects, including Div; `@Parallel` is invalid (`E0620`). Allow immutable captures and locally handled operations. Reject outside mutable/live handlers and resource operations; apply each combinator's access contract.

Pure map/find/fold follow their reference evaluation. Disjoint-write join/for_each follow their [completion rule](#declarative-data-parallelism-and-concurrency-bounding); no universal left-fold equivalence applies.

#### Deterministic Reductions and Bit-Exact Floating-Point Trees

`Parallel::fold(items, init_acc, fold_local, merge_acc)` has this reference evaluation:

1. Partition the input by increasing index into consecutive groups of at most 64 elements.
2. For each group in order, call `init_acc()` once and perform `fold_local` from left to right over that group. Finish all groups before starting merges.
3. Merge adjacent group results from left to right at each level. An unpaired final result advances unchanged. Repeat levels until one result remains.
4. Empty input calls `init_acc()` exactly once and returns it. No merge is performed for fewer than two groups.
5. The first fault in this reference order is the visible fault; later reference operations need not be evaluated. A dependent operation is not evaluated after its input failed. A fold-local fault records the source element index; initialization and merge faults use `PanicInfo.index = None`.

This rule applies to non-associative operations as well. Floating-point addition is permitted but is not claimed to be associative or equal to ordinary sequential left folding. Given fixed primitive numeric semantics, the tree and result do not change with scheduling or worker count.

```ril
let total = Parallel::fold(
    [1.0, 2.0, 3.0],
    init_acc: \-> 0.0,
    fold_local: \acc, x -> acc + x,
    merge_acc: \left, right -> left + right,
)
assert(total == 6.0)
```

#### Observational Equivalence and Short-Circuit Determinism

`map` follows element order. `find`, `first`, and `any` stop at the first decisive match or fault in that order. A match suppresses everything to its right; skipped branches may have no outside-observable effects.

#### Canonical Leftmost Panic Precedence Rule

- A pure branch's panic/double fault first becomes a local terminal outcome. Propagate only faults visible in reference evaluation; skipped rightward faults cannot fail the parent.
- Branches own their mutable state and cleanup. Abandoned cleanup must not affect an outside-observable resource (`E0605`).

Wait for all started branches. Propagate the selected panic; a selected double fault fatally fails the owning task or aborts an unsupervised program. Never resume a failed branch or restart abandoned cleanup.

```ril
let found = [0, 1] |> Parallel::find(\x -> {
    if x == 0 { true } else { panic("right branch") }
})
assert(found == Some(0))               -- Even if the right branch ran speculatively
```

The same reference-visibility rule applies if the skipped right branch suffers a double fault in branch-local cleanup. There is no exception that lets speculative fatal outcomes change an otherwise successful leftmost result.

#### Lightweight Divide-and-Conquer (Parallel::join)

`Parallel::join(a, b)` returns `(a(), b())`; `join3` returns three results. Invoke each branch once and wait for all branches.

- Share immutable reads. Temporary parent-data writes require disjoint write/read and write/write regions (`E0619`). Check actual captures; distinct names/indices do not prove separation.
- The parent suspends access to lent regions until completion; other tasks cannot access them. Branch invocation authority is confined and does not create a lasting owner.

#### Declarative Data Parallelism and Concurrency Bounding

- **for_each**: `cells !> Parallel::for_each(\mut cell -> { ... })` explicitly lends each writable element to one invocation. Every element's writable reachable region must be disjoint from every other invocation's reads/writes (`E0619`). Immutable elements or unknown overlapping aliases are rejected; outside mutable captures are rejected (`E0605`).
- **Completion**: join/join3/for_each finish every independent invocation and retain its writes. Then report double fault before panic, breaking ties by branch/index order. There is no rollback or sequential-short-circuit partial-state guarantee.
- **map_bounded**: A positive `max_concurrency` bounds active evaluations without changing pure reference semantics. A non-positive bound panics before any callback invocation.

```ril
type Cell = { mut count: int }
let mut cells = [Cell.{ count: 1 }, Cell.{ count: 2 }]
cells !> Parallel::for_each(\mut cell -> { cell.count *= 2 })
assert(cells[0].count == 2 && cells[1].count == 4)

let original = Cell.{ count: 0 }
let repeated = (original, original)
let mut copy = ^mut clone(repeated)
-- Parallel::join(\-> { copy.0.count += 1 }, \-> { copy.1.count += 1 })
-- Error [E0619]: both branches would write the same copied origin
copy.0.count += 1                     -- Sequential access is valid
```

#### The Absolute Effect-Free Parallel Invariant

Apply effect, access, and termination checks transitively through calls and handlers. Div cannot be handled away. Resource endpoint operations are not pure parallel operations. Only join/for_each grant confined outside write authority; no live aliases escape.

### Structured Concurrency Channels

```ril
use ril/concurrent::{scope, TaskFault}
use ril/concurrent/channel

fn one_message() -> Result<int, TaskFault> @Async {
    scope \mut s -> {
        let (tx, mut rx) = Channel::bounded<int>(1)
        let producer = s.fork(\-> {
            -- Channel::close(tx)     -- Error [E0603]: a child clone-source borrow cannot consume the owner
            let mut local_tx = clone(tx)
            (local_tx !> Channel::send(42))
                ?? \_error -> panic("receiver closed")
            Channel::close(local_tx)
        })
        -- Channel::close(tx)         -- Error [E0603]: producer still holds a clone-source borrow
        let value = (rx !> Channel::recv())
            ?? \_error -> panic("sender closed")
        producer.join()?
        Channel::close(tx)
        Ok(value)
    }
}
```

#### Normative Rules for Structured Channels


The following declarations describe the channel module's contracts (opaque declaration-unit forms):

```ril
pub type Sender<T>
pub type Receiver<T>
pub type Detached<E>
pub type ChannelError { Closed }
pub fn bounded<T>(capacity: int) -> (Sender<T>, Receiver<T>) @Fiber
pub fn send<T>(mut endpoint: Sender<T>, value: T) -> Result<(), ChannelError> @Fiber &mut
pub fn recv<T>(mut endpoint: Receiver<T>) -> Result<T, ChannelError> @Fiber &mut
```

Sender/Receiver/Detached are scope-owned opaque resources. Immutable descriptors may enter `let`; protocol state is external and effect-accessed. These resource contracts do not apply to ordinary data.

| Access or copy | Contract |
| :--- | :--- |
| Send/receive | Writable endpoint, `@Fiber &mut`; one owning task (`E0603`) |
| `clone(Sender<T>)` | `@Fiber`; independent task-local endpoint authority, same channel; no resource-graph isolation guarantee |
| Immutable Sender captured by a child | Clone-source only; no send/close/detach or acquisition of owner authority (`E0603`), even through aggregates/closures |
| Owner close/detach while borrowed | Suspended until every borrowing task's terminal join or the scope's child barrier (`E0603`) |
| Scheduling progress, dropped Task, last textual use | Do not end a clone-source borrow |
| Clone Receiver/Detached; endpoint `clone_immut` | `E0530`, including inside containers |
| Endpoint `derive` | `E0536`, including inside containers |

```ril
-- Within an owning scope; rx has no other usable alias:
let ticket = Channel::detach(mut rx)
-- rx !> Channel::recv()               -- Error [E0603]: authority was transferred
-- clone(ticket)                      -- Error [E0530]: detached authority cannot be duplicated
-- The receiving task can consume ticket once with Channel::attach(ticket).
```

```ril
-- Within one owning scope; resource_rx is an exclusive endpoint and control_tx accepts its Detached descriptor.
let ticket = Channel::detach(mut resource_rx)
let sent = control_tx !> Channel::send(ticket)
match sent { Ok() -> {}, Err(_error) -> {} }
-- Channel::attach(ticket)             -- Error [E0603]: both send outcomes consumed the ticket
```

| Operation (`@Fiber`) | Authority change |
| :--- | :--- |
| `detach(mut endpoint)` | Consume exclusive endpoint; return non-clonable `Detached<Endpoint>` |
| `attach(ticket)` | Consume once; obtain writable endpoint in receiving task |
| Enter `send(ticket)` after argument evaluation | Consume ticket on every outcome; pending send owns it |
| Enqueue / successful receive | Ownership passes to queue / receiver |
| `Err(Closed)` or cancellation before enqueue | Close submitted endpoint once; never restore ticket |
| Receiver close | Close unreceived queued detached endpoints once |

Detach rejects other usable aliases/views/captures and invalidates old paths (`E0603`). Only detached descriptors are transferable resource payloads; `mut`/`^mut` alone never transfer. Transfers and cross-task clones stay within the owning scope's descendants (`E0606`), independently of GC.

Payloads may be scalars, immutable ordinary data (even with field `mut` markers), or one-use detached descriptors. Live data, mutable environments, ordinary write authority, and hidden non-transferable resources are `E0602`.

```ril
-- Within an owning scope; writable rx receives Result<int, str> payloads.
match (rx !> Channel::recv()) {
    Ok(business) -> { let _ = business ?? \_error -> 0 },
    Err(_error) -> {},
}
-- match (rx !> Channel::recv()) { Ok(_) -> {}, Err(_) -> {} }
-- Error [E0720]: only the transport result was inspected
```

| Fallible payload event | Outstanding inspection obligation |
| :--- | :--- |
| Successful send / receive | Passes to queue / received value |
| Send returns `Err(Closed)` | Stays with sender's original value/aliases; no implicit payload return |
| Inspect send/recv's outer Result | Does not inspect a payload Result |
| Normal completion, including another business `Err` | Must preserve or discharge the obligation (`E0720`) |
| Normal receiver close / scope exit | Cannot discard possibly uninspected queued Results (`E0720`) |
| Receive returns `Err(Closed)` | Queue is empty |
| Panic, cancellation, effect abort | Ordinary abnormal-unwinding exemption |

Aliases share one obligation; transmission does not create an independent copy.

| Operation | Result and ordering |
| :--- | :--- |
| `send` | `Result<(), ChannelError>`; closed receiver gives `Err(Closed)` |
| `recv` | `Result<T, ChannelError>`; drain queue, then `Err(Closed)` after all senders close |
| `bounded` | Positive capacity limits queued messages; invalid capacity panics before creation |

Successful sends retain each sender's order; different senders have no global order.

| Closing or cancellation | Rule |
| :--- | :--- |
| `Channel::close` | `@Fiber`; consumes the descriptor's authority and invalidates its aliases |
| Task termination | Close writable local endpoints |
| Scope exit | Close remaining descriptors after the child barrier |
| Automatic close | Structured boundary's `@Fiber` contract; not `on_close` or a separate `let scoped` contract |
| Immutable clone-source Sender | Open until close/scope exit; EOF never depends on GC |
| Cancel blocked send/recv | Non-resumable scope exit; no fabricated message/error. Producer failure wakes a body blocked on recv |

### Arrow-Only Law of Effects

Completed evaluation leaves a value. Passive data carries no direct effect annotation; a stored callable still carries the obligations of a later invocation.

Attaching effects directly to passive data is rejected. A record field or tuple component uses `E0333`; an ordinary value binding or non-callable array expression uses `E0613`. A callable stored in any of these positions can retain its own effect obligations:

```ril
-- -----------------------------------------------------------------------------
-- Negative Examples: Prohibited Value Effect Annotations (E0613)
-- -----------------------------------------------------------------------------
-- type BadField = { data: int @Io }            -- Error [E0333]: FieldComputationAnnotationError: record field 'data' has value type 'int'; raw effects cannot reside on values
-- type BadTuple = (str @Io, int)               -- Error [E0333]: FieldComputationAnnotationError: tuple component has value type 'str'; raw effects cannot reside on values
-- type BadArray = []int @Async                 -- Error [E0613]: ValueEffectAnnotationError: array element has value type 'int'; raw effects cannot reside on values

-- fn test_binding_error() @Io {
--     let bad_bind: str @Io = "hello"          -- Error [E0613]: ValueEffectAnnotationError: binding 'bad_bind' specifies effect '@Io'; values in normal form carry no latent effects
--     let @Io bad_prefix = "hello"             -- Error [E0613]: ValueEffectAnnotationError: binding pattern specifies effect '@Io'; misplaced effect annotation
-- }

-- -----------------------------------------------------------------------------
-- Positive Examples: Arrow-Only Law
-- -----------------------------------------------------------------------------
type ValidService = {
    name: str,                                  -- Pure value at rest
    fetch_data: fn() -> str @Io,                -- OK: callable arrow carrying latent effect
}

fn test_valid_binding() @Io {
    let result: str = Io::read_line()           -- OK: expression executes @Io; resulting value is pure 'str'
    assert(result != "")
}
```

---

## Compile-Time Computation and Totality

### Static Type Values and Type Quotation

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
-- let bad_t = int                     -- Error [E0319]: BareTypeInExpressionContextError: bare type 'int' used in expression context; wrap in 'type<int>'
-- let bad_inferred = typeof (1 + 2)   -- Error [E0319]: BareTypeInExpressionContextError: bare 'typeof' operator used in expression context; wrap in 'type<typeof (1 + 2)>'
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
halt type Identity = \T -> type<T>              -- OK: type-producing function
meta fn size_of<T>(t: type<T>) -> int { byte_size(t) } -- OK: reflection produces a value
halt fn checked_increment(n: int) -> int { n + 1 } -- May panic at int's maximum
halt fn yield_once() @Fiber { Fiber::yield() }     -- No promise about external scheduling progress
-- halt fn forever() { loop {} }                  -- Error [E0820]: uncertified local loop
-- meta let BAD_SUM = 127i8 + 1i8                 -- Error [E0831]: panic during static evaluation
```

| Static definition | Result / restriction |
| :--- | :--- |
| Type declaration/function | May synthesize and return types; effects/capabilities forbidden (`E0335`) |
| `meta fn` | Returns values, never `Type`/`type<...>` (`E0812`); effect/state annotations forbidden (`E0813`) |
| `type<T>` input to `meta fn` | Immutable, non-generative reflection token; cannot synthesize or mutate types |

Both run with empty effect/capability domains. Local `let`, `if`, `match`, pure meta helpers/combinators, and recursion are supported.

| `halt` boundary | Guarantee |
| :--- | :--- |
| `halt fn` | Finite local computation; panic, early return, and effect abort remain possible |
| I/O, system operations, child waits | Progress conditional on completion; waiting alone is not Div |
| Transitive calls/callbacks/handlers/cleanup | No Div in the current invocation |
| `halt type` | Finite symbolic computation; invalid inputs/static defects can still fail |

| Finite-iteration case | Required proof |
| :--- | :--- |
| `for` | Finite collection/range |
| `while`/`loop` | Every continuing path makes the next condition false, or advances one counter toward a stable finite bound |
| Counter progression | Nonzero step in a fixed direction; continuation stays on the corresponding side of the bound |
| Equality exit (`while` or `loop`) | Initial value and step known to reach the exit |
| `next` | Same progress obligation |
| Other writes, aliases, callbacks, handlers | Cannot invalidate the counter/bound |
| Arithmetic | Checked overflow is finite panic; wrapping updates do not qualify |

| Recursive case | Rule |
| :--- | :--- |
| Ordinary run-time cycle | Contributes Div |
| `halt` group | Each cycle strictly decreases a nonnegative integer under a lower-bound guard, or takes a proper subpart of a known finite acyclic structure |
| Mutual recursion | Preserve the same decreasing argument/structure relation throughout the cycle |
| Recursive type unfolding | Not structural decrease |
| Calls outside the group | Keep their obligations; all meta/type helpers reached by `halt type` must also be finite |

Uncertified run-time loops contribute Div; unmarked static loops/recursion use their budget without Div. An uncertified `halt` body is `E0820`. Neither an annotation, an empty effect row, nor a budget proves termination.

| Static evaluation | Budget / failure |
| :--- | :--- |
| Each root evaluation | Configured positive budget, including certified computations |
| Meta/type function entry, static callback entry, loop iteration | Consume one unit each |
| Next charged step with no budget | `E0811` |
| Alias cycle | Separate `E0313` check |
| Failed `assert` / other panic | Static `E0830` / `E0831` |

```ril
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
-- meta fn bad_type_gen() -> type<int> {       -- Error [E0812]: MetaTypeReturnProhibitedError: 'meta fn' cannot return 'type<...>'; monopolized by type functions
--     type<int>
-- }
-- halt type BadEffect = \T -> type<T> @Async  -- Error [E0335]: TypeFunctionComputationAnnotationError: type functions cannot declare algebraic effects
-- meta fn bad_eff() -> int @Io { 0 }          -- Error [E0813]: MetaComputationAnnotationError: 'meta fn' cannot declare algebraic effects
-- type BadInfinite<T> = BadInfinite<T>        -- Error [E0313]: cyclic alias without nominal or sum indirection
-- type Spin = \T -> Spin<T>
-- type NeverFinishes = Spin<int>             -- Error [E0811]: recursive type-function evaluation exhausts its budget
```

### Disjoint Call Families, Evaluation Budgets, and Branch Pruning

```ril
eff Audit { write(str) -> () }
fn logged_worker(x: int) -> int @Audit { Audit::write("work"); x }

fn dispatch_worker<run: bool>(f: fn(int) -> int, val: int) -> int {
    if run { f(val) } else { val }
}

fn test_specialization() {
    assert(dispatch_worker<false>(logged_worker, 10) == 10) -- OK: callback is not invoked
}
fn run_logged() -> int @Audit { dispatch_worker<true>(logged_worker, 10) }
-- fn hidden_log() -> int { dispatch_worker<true>(logged_worker, 10) } -- Error [E0612]
```

| Call family | Permitted calls |
| :--- | :--- |
| Type function | Other type functions and `meta fn`; no run-time `fn` (`E0810`) |
| Run-time function | No type-function invocation (`E0810`) |
| Both phases | Pure arithmetic/comparison, `len`, `assert`, pure Array/String/Map combinators |

Static callbacks capture symbolic constants. Mutable resources, handlers, and ordinary run-time calls have no phase-polymorphic exception. Static budget exhaustion is `E0811`.

| Condition | Invocation effects, state, escape, authority use |
| :--- | :--- |
| Static boolean | Selected branch only |
| Run-time boolean | Both branches' possible obligations |

Both branches still obey syntax, name resolution, and ordinary type compatibility. Type tokens expose no callable-value effects/provenance; no built-in `is_pure` exists.
### Unified Tripartite Introspection

Ril unifies compile-time introspection across all three composite data forms (Records, Sum Types, Tuples) under a single operator pair: `keyof T` and constituent projection `T.(K)`.

```ebnf
(* TypeProjection is defined in its earlier grammar production. *)
(* TupleIndex is defined in its earlier grammar production. *)
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
    -- get_field(user, key)             -- Error [E0810]: actual key is not statically known
}
```

- `K: keyof T` is a static string key for records/sums, or an integer tuple position; it is not a run-time literal type.
- `key: K` requires an argument statically equal to K and permits inferring K from it. Both names denote that key in the body.
- K is not an ordinary data type: `[]K` is `E0301`. Check membership after inference (`E0323`); unknown run-time keys are `E0810`.

| Value projection | Requirement |
| :--- | :--- |
| `record.(key)` / `record.("name")` | Static key; preserve reference permissions/origins; bracket indexing is `E0324` |
| Tuple | Static positional index; excluded by the example's record constraint |
| Sum payload | `match` or variant narrowing; membership in `keyof S` alone is insufficient (`E0301`) |

An immutable run-time string is not a static key. Sum type keys describe possible payload shapes, not fields present in every value.

#### Universal Constituent Projection
For any composite type $T$ and coordinate key $K \in \text{keyof } T$, `T.(K)` statically projects the corresponding constituent shape:
- **Records**: `User.id` or `User.("id")` resolves to the declared field type.
- **Sum Types**: `UiEvent.Click` or `UiEvent.("Click")` resolves to the variant payload type under Constructor-Tuple Equivalence:
  - Multi-field variants ($n \ge 2$): Resolves to anonymous product tuple `(T1, ..., Tn)`.
  - Single-field variants ($n = 1$): Resolves to scalar type $T_1$ (Ril strictly has no 1-tuples).
  - Unit constructors ($n = 0$, declared `Variant()`): Resolves to unit `()`.
  - Nullary tags (declared `Variant`): Resolves to unit `()` as its injection domain, ensuring generic eliminators `fn(T.(K)) -> R` remain universally callable.
- **Tuples**: `Pair.0` or `Pair.(0)` resolves to the component type at positional index $K$.

#### Symmetrical Mapped Comprehensions
- **Mapped Records**: `{ [K in Expr]: TypeExpr }` requires static `[]str`; integer keys are `E0341`. Duplicate/invalid labels are `E0203`/`E0102`; ADT tables may use PascalCase constructor labels.
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
-- type BadRecordKeys = { [K in [0, 1]]: int } -- Error [E0341]: InvalidRecordKeySortError: mapped record comprehension requires '[]str' keys, found '[]int'
-- type BadTupleKeys = ( [I in ["a", "b"]]: int ) -- Error [E0342]: InvalidTupleKeySortError: mapped tuple comprehension requires '[]int' keys, found '[]str'
-- type Bad1Tuple = ( [I in [0]]: int )       -- Error [E0343]: SingleElementTupleProhibitedError: mapped tuple comprehension produced single-element tuple (Ril strictly has no 1-tuples)
```

### Structural Type Pattern Matching

Type functions deconstruct types using standard `match` over quoted type expressions `type<T>` without dedicated macro dialects:

```ebnf
TypeMatchExpr    ::= "match" "type" "<" TypeExpression ">" "{" [ TypeMatchArm { "," TypeMatchArm } [ "," ] ] "}"
TypeMatchArm     ::= TypePattern { "|" TypePattern } [ "if" Expression ] "->" Expression
TypePattern      ::= "type" "<" TypePatternInner ">" | "_"
TypePatternInner ::= RigidNominalPattern | TypeTuplePattern | TypeRecordPattern
                   | ArrayPattern | MapPattern | PrimitivePattern | LiteralPattern | Wildcard | "let" ( PascalCase | Wildcard )
```

- **Scoped Pattern Variables (`let U`)**: A `let U` binder inside `type<P>` introduces an immutable type variable scoped strictly to the arm's guard and RHS expression. `U` MUST be `PascalCase` (`E0101`).
- **Linearity Invariant**: Pattern variables MUST be linear; repeating the same identifier within a pattern branch is statically rejected (`E0203: DuplicateDeclarationError`). Multi-position equality is asserted via explicit guards (`if type<A> == type<B>`).
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
--     type<(let M)<let U>> -> type<U>,         -- Error [E0306]: KindMismatchError: rigid type pattern cannot bind constructor '(let M)' as a higher-kinded pattern variable
--     _                    -> type<never>,
-- }
```

### Static Parameter Sorts and Adaptation Rules

Type functions accept the following parameter sorts and constraints:

- **Bare Types (`\T` or `\T: Type`)**: Accepts static type expressions. Unannotated parameters default to sort `Type`.
- **Const Values (`\param: ValueType`)**: Accepts compile-time known constants (literals, `meta let`, statically foldable expressions). Passing runtime variables raises `E0810`.
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

`meta let` and `meta fn` evaluate in the pure static domain. Results can be used as immutable run-time constants. Type functions can consume these values to select shapes. Arithmetic on sizes follows the ordinary integer rules.

```ril
meta fn align_to(offset: int, alignment: int) -> int {
    assert(offset >= 0 && alignment > 0)
    assert((alignment & (alignment - 1)) == 0)
    (offset + alignment - 1) & ~(alignment - 1)
}
halt type BufferShape = \capacity: int -> type<{
    data: [capacity]u8,
    used: int,
}>
meta let CAPACITY = align_to(60, 16)
type Buffer = BufferShape<CAPACITY>
meta let _ = assert(CAPACITY == 64)
-- meta let _ = assert(CAPACITY == 32) -- Error [E0830]: failed static assertion
```

An array field is a reference: `[4]u8` does not mean four inline padding bytes. Shape declarations promise no packed order, offsets, pointer size, or external binary layout.

`byte_size(type<T>)` measures T's value/handle on the selected abstract target, not its reachable graph. Such static queries may be target-dependent.

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
-- use math/geometry::{PI}              -- Error [E0201]: PrivateItemAccessError: symbol 'PI' is private to module 'math/geometry'
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
-- use ril/crypto as hash               -- Error [E0101]: InvalidIdentifierCasingError: module namespace alias must be PascalCase, found 'hash'

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
-- let bad = sha256("data")              -- Error [E0204]: UnresolvedIdentifierError: unresolved identifier 'sha256'
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
-- let current_time = Clock::now()      -- Error [E0202]: TopLevelSideEffectError: top-level declaration must be a pure constant expression
-- let db = Database::connect("db.loc") -- Error [E0202]: TopLevelSideEffectError: top-level declaration cannot invoke runtime I/O or effects
-- let top_parse = parse_id("10")?      -- Error [E0205]: QuestionMarkOutsideFunctionError: postfix '?' operator used outside function or closure body; no enclosing activation frame to receive early return
```

### Test Conventions and Execution Protocol

Test entry points are ordinary public functions conforming to the naming prefix `test_*` and returning either `()` or `Result<(), E>`. Test functions evaluate within isolated activation frames and enforce domain invariants via standard assertions:

- **Pure & Direct Tests**: Functions returning `()` verify invariants using deterministic runtime panics on breach (`assert`).
- **Fallible Tests**: Functions returning `Result<(), E>` enable cascading error propagation via postfix `?`. Returning `Err(e)` indicates test assertion failure.
- **Hermetic Scoped Mocking**: Environmental algebraic effects are mocked within standard lexical blocks `{ with HandlerSpec; logic }`. The handler is automatically popped upon exiting the block. Missing handlers are rejected statically; a mock handler may explicitly panic on an unexpected but handled request.
- **Panic Isolation Assertion**: Asserting that defective operations trigger deterministic runtime panics is evaluated across structured concurrency task boundaries (`s.fork` inside `scope`), capturing faults into `TaskFault::Panicked` without violating synchronous frame panic isolation.
- **Resource Lifecycle**: Ephemeral and in-memory test resources use `let scoped` bindings, guaranteeing strict LIFO destruction. Effectful I/O transactions utilize higher-order wrapper functions.

```ril
use ril/array::{push}

-- Direct unit test returning ():
pub fn test_array_push() -> () {
    let mut items = [1, 2]
    items !> push(3)
    assert(len(items) == 3, "expected 3 items")
}

-- Fallible unit test with '?' error cascade:
pub fn test_parse_pipeline() -> Result<(), str> {
    let raw = "100"
    let parsed = parse_int(raw)?
    assert(parsed == 100, "expected parsed integer 100")
    Ok()
}

-- Hermetic sandbox mock testing via scoped handler block:
eff Database {
    query(sql: str) -> Result<str, str>,
}

pub fn test_user_query() -> Result<(), str> {
    let outcome = {
        with Database::query(sql) -> {
            if sql == "SELECT user FROM users WHERE id = 1" {
                resume Ok("Alice")
            } else {
                -- Hermetic Sandbox: unexpected calls trigger deterministic defect panic
                panic("Unexpected mock query: {sql}")
            }
        }

        let user = Database::query("SELECT user FROM users WHERE id = 1")?
        assert(user == "Alice", "user mismatch")
        Ok()
    }
    outcome
}

-- Scoped resource cleanup following strict LIFO order:
pub fn test_scoped_cleanup() -> Result<(), str> {
    let mut trace: []str = []
    {
        let scoped mut res = Resource.{
            name: "test_db",
            on_close: \-> trace !> push("db_closed"),
        }
        trace !> push("test_executed")
    }
    assert(trace == ["test_executed", "db_closed"], "cleanup must follow LIFO order")
    Ok()
}

-- Defect panic assertion via structured concurrency boundary:
use ril/concurrent::{scope, TaskFault}

pub fn test_out_of_bounds_defect() -> Result<(), str> @Concurrent {
    let outcome = scope(\mut s -> {
        s.fork(\-> {
            let arr = [1, 2]
            let _ = arr[5]             -- Triggers defect panic: index out of bounds
            Ok()
        })
        Ok()
    })

    match outcome {
        Err(TaskFault::Panicked(info)) -> {
            assert(info.message == "index out of bounds (index 5, length 2)", "panic message mismatch")
            Ok()
        },
        _ -> panic("expected operation to panic, but completed normally"),
    }
}
```

### Program Entry Point

Executable programs define one root `main` function. Its declared built-in system effects are provided by the program environment; user-defined effects still require handlers. The examples below are alternatives, not two definitions in one program. Prelude print/println have `@Fiber`, and file-I/O examples use the corresponding leaf-I/O contract:

```ril
pub fn main() -> () @Fiber {
    println("Hello, Ril!")
}

-- Fallible main:
pub fn main() -> Result<(), str> @Fiber {
    let config = File::read("config.json")?
    if config == "" {
        Err("empty configuration")     -- Runtime halts with non-zero exit code (1)
    } else {
        Ok()                            -- Exits cleanly with status code (0)
    }
}
```

### Standard Prelude Built-ins

The following types, functions, and core modules are implicitly available in every compilation unit without explicit `use` statements:

| Item | Kind | Description |
| :--- | :--- | :--- |
| `Option<T>`, `?T` | Sum Type | Optional value: `Some(T)` or `None` |
| `Result<T, E>` | Sum Type | Fallible operation outcome: `Ok(T)` or `Err(E)` |
| `Immut<T>` | Type | Explicit immutable ordinary data; nested outer Immut qualifiers normalize |
| `[K: V]` | Type | Built-in associative map |
| `Array` | Module | Standard dynamic array combinators and mutation primitives (`push`, `pop`, `map`, `filter`, `fold`, `contains`, `reverse`) |
| `Map` | Module | Standard associative map combinators and access primitives (`get`, `set`, `remove`, `contains`, `keys`, `values`) |
| `Set` | Module | Standard unique set operations and algebraic combinators (`contains`, `insert`, `remove`, `union`, `intersect`, `diff`) |
| `String` | Module | Standard string operations and character inspection (`split`, `trim`, `contains`, `replace`, `starts_with`, `ends_with`) |
| `inner(wrapper)` | Function | Extracts underlying value from nominal wrapper `type W(T)` |
| `clone(x)` | Function | Deep isolated ordinary-data copy; sender resources use their separate effectful contract |
| `clone_immut(x)` | Function | Copies eligible ordinary data as immutable data into `Immut<T>` |
| `derive(base, recipe)` | Function | Confined graph derivation with immutable input/output and unchanged immutable sharing |
| `len(coll)` | Function | Returns element count of string, bytes, array, map, or set |
| `panic(msg)` | Function | Initiates deterministic runtime panic unwinding |
| `assert(cond, msg)` | Function | Verifies invariant; panics on breach |
| `print(s)`, `println(s)` | Functions | Writes text to standard output with `@Fiber` |

```ril
-- Ambient Prelude Collection Modules (no 'use' required):
let mut list = [1, 2]
list !> Array::push(3)                  -- OK: 'Array' is ambiently available from prelude
let evens = list |> Array::filter(\x -> x % 2 == 0)

let config_map: [str: int] = ["timeout": 5000, "retries": 3]
let timeout_val = config_map |> Map::get("timeout") -- OK: 'Map' is ambiently available

let words = "hello,world,ril" |> String::split(",") -- OK: 'String' is ambiently available
let tags: Set<str> = Set::from(["system", "kernel"]) -- OK: 'Set' library module is ambiently available from prelude

-- Nominal Unwrapping via inner():
type UserId(int)
let uid = UserId(1001)
let raw_id: int = inner(uid)           -- 1001

-- Deep Mutable Cloning via clone():
let original = [1, 2, 3]
let mut detached = clone(original)
detached !> Array::push(4)             -- Mutates 'detached'; 'original' remains [1, 2, 3]

-- Immutable Copy via clone_immut():
let immutable: Immut<[]int> = clone_immut(original)
-- immutable !> Array::push(5)            -- Error [E0520]: MutabilityLaunderingError: cannot mutate permanently immutable Immut<T>

-- Functional Derivation via derive():
let base_cfg = .{ theme: "dark", retries: 3 }
let updated_cfg = base_cfg |> derive \mut draft -> {
    draft.theme = "light"
}
assert(base_cfg.theme == "dark" && updated_cfg.theme == "light")

-- Length Inspection via len():
let count = len("hello")               -- 5 (Unicode scalar count)
let array_len = len([10, 20, 30])      -- 3

-- Invariants and Panic Primitives:
assert(len(original) > 0, "must not be empty") -- OK
if len(original) == 0 {
    panic("unreachable state reached")  -- Initiates deterministic runtime panic
}
```

### Mandatory Inspection of Fallible Results

```ril
fn save_profile(user_id: int) -> Result<(), str> {
    if user_id <= 0 { Err("invalid id") } else { Ok() }
}

fn process_request(id: int) -> Result<(), str> @Fiber {
    -- Prohibited: discarding fallible Result without inspection
    -- save_profile(id)                 -- Error [E0720]: UnusedFallibleResultError: unused fallible Result must be handled

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
| Binding, alias, wrapping, aggregate, Task | Preserve one obligation, not one per name |
| Deep copy | Preserve copied Results' obligations; copying is not inspection |
| `_`, overwrite, removal, lost last path | Do not discharge |
| Outer tag test | Does not inspect an inner Result |
| `?` | Propagates failure to the enclosing callable |
| Normal completion, including `Err` return | Cannot abandon other outstanding Results |
| Abnormal unwinding | May discard; structured cancellation keeps its specified rules |

---


## Diagnostic Error Codes Summary

| Code | Diagnostic Name | Normative Condition |
| :---: | :--- | :--- |
| **`E0101`** | `InvalidIdentifierCasingError` | Identifier casing style violates grammatical role requirement |
| **`E0102`** | `MalformedIdentifierSyntaxError` | Malformed identifier casing/underscores, invalid literal escape/scalar, or invalid generated field label |
| **`E0103`** | `PatternCasingCollisionError` | Pattern binding position contains illegal casing causing semantic collision |
| **`E0201`** | `PrivateItemAccessError` | Accessing or importing unexported private module symbol |
| **`E0202`** | `TopLevelSideEffectError` | Top-level declaration contains non-constant runtime side effects |
| **`E0203`** | `DuplicateDeclarationError` | Duplicate same-scope binding/handler operation or ambiguous unqualified constructor abbreviation |
| **`E0204`** | `UnresolvedIdentifierError` | Reference to an unavailable identifier, including use/publication of a helper before its required captures initialize |
| **`E0205`** | `QuestionMarkOutsideFunctionError` | Using postfix '?' operator outside an enclosing function or closure body (no enclosing activation frame to receive early return) |
| **`E0301`** | `TypeMismatchError` | Expression type incompatible with expected type |
| **`E0302`** | `UnexpectedFieldError` | Closed record supplied with undeclared fields |
| **`E0303`** | `NonExhaustiveMatchError` | Nonexhaustive match or refutable pattern where an unguarded binding, for, or handler requires an irrefutable pattern |
| **`E0304`** | `UnreachableMatchArmError` | Pattern match arm is statically unreachable due to preceding exhaustive patterns or GADT index constraints |
| **`E0305`** | `NominalTypeMismatchError` | Mismatched nominal type wrapper identities |
| **`E0306`** | `KindMismatchError` | Mismatched higher-kinded type constructor or sort constraint |
| **`E0307`** | `MissingFieldError` | Record projection or construction expression lacks required declared field |
| **`E0308`** | `OpaqueBoundaryViolationError` | Attempting to unpack, penetrate with `inner()`, or pattern deconstruct an opaque type externally |
| **`E0309`** | `VacuousBindingError` | 'let' pattern binds zero variables (excluding explicit wildcard discard 'let _ = expr') |
| **`E0310`** | `InvalidatedNarrowingAccessError` | Accessing identifier whose flow narrowing was invalidated by reassignment or mutation |
| **`E0311`** | `ContradictoryNarrowingError` | Narrowing predicate contradicts an already active refinement |
| **`E0312`** | `TupleIndexOutOfBoundsError` | Static tuple index projection exceeds bounds of tuple type |
| **`E0313`** | `CyclicTypeAliasError` | Structural type aliases form a cyclic dependency without nominal or sum indirection |
| **`E0314`** | `ArityMismatchError` | Argument count differs from the ordinary function or constructor/pattern arity |
| **`E0315`** | `EscapingLocalNominalTypeError` | An in-scope function-local nominal, opaque, or sum identity escapes through a returned value or callable's type |
| **`E0316`** | `NonTrailingDefaultGenericParamError` | Generic parameter without default follows generic parameter with default |
| **`E0317`** | `FunctionDefaultGenericProhibitedError` | Function generic parameter declares default type or value argument |
| **`E0318`** | `LiteralTypeProhibitedError` | Value literal used as a type instead of a const argument or a tagged sum state |
| **`E0319`** | `BareTypeInExpressionContextError` | Bare type name used in expression context without enclosing `type<...>` wrapper |
| **`E0320`** | `ForwardTypeDefaultReferenceError` | Generic default parameter expression contains forward reference or circular dependency |
| **`E0321`** | `NonDivergentElseError` | A guarded binding's else block can complete normally instead of having type never |
| **`E0322`** | `WildcardExpressionError` | Standalone wildcard '_' used in expression position outside pattern binding or discard context |
| **`E0323`** | `ConstGenericSortMismatchError` | Const/static-key argument has the wrong sort or is not a member of its keyof constraint |
| **`E0324`** | `DynamicRecordIndexProhibitedError` | A record is accessed with bracket indexing or a non-static computed key |
| **`E0325`** | `DuplicateArgumentError` | Duplicate named argument supplied in function or constructor call |
| **`E0330`** | `BareEffectTypeAliasError` | Attempting to alias an effect ('@Eff') under 'type E = ...' instead of 'eff' declaration |
| **`E0331`** | `BareCapabilityTypeAliasError` | Attempting to alias a capability ('&mut', '&^mut') under 'type C = ...' |
| **`E0332`** | `VariantComputationAnnotationError` | Attaching '@Eff' or '&Cap' directly to a sum type variant constructor |
| **`E0333`** | `FieldComputationAnnotationError` | Attaching '@Eff' or '&Cap' directly to a record field or tuple component |
| **`E0334`** | `GenericComputationConstraintError` | Constraining a generic parameter with an effect ('<T: @Io>') or capability ('<T: &mut>') |
| **`E0335`** | `TypeFunctionComputationAnnotationError` | Declaring '@Eff' or '&Cap' on a pure compile-time type function ('type', 'halt type') |
| **`E0341`** | `InvalidRecordKeySortError` | Supplying integer keys to mapped record comprehension '{ [K in Expr]: ... }' (requires '[]str') |
| **`E0342`** | `InvalidTupleKeySortError` | Supplying string keys to mapped tuple comprehension '( [I in Expr]: ... )' (requires '[]int') |
| **`E0343`** | `SingleElementTupleProhibitedError` | Mapped tuple comprehension evaluated over an index array of length 1 (Ril strictly has no 1-tuples) |
| **`E0401`** | `ValueTypeMutableBorrowError` | Attempt to declare or pass a value type as a mut/^mut parameter |
| **`E0402`** | `ValueTypePinnedMutError` | Attempting to give a value type interior authority with `let mut` or `var mut` |
| **`E0403`** | `VarParameterProhibitedError` | Attempting to declare a function parameter with `var` |
| **`E0404`** | `MutableParameterDefaultProhibitedError` | A mut/^mut parameter specifies a default value argument |
| **`E0501`** | `ImmutableReassignmentError` | Reassigning an immutable `let` binding |
| **`E0502`** | `PinnedHandleReassignmentError` | Reassigning a pinned mutable handle `let mut` or borrowed `mut` parameter |
| **`E0510`** | `MissingCapabilityAnnotationError` | Missing required concrete invocation capability or local writable-sharing marker, including known inherited state, direct reads, creation, or retention |
| **`E0520`** | `MutabilityLaunderingError` | Granting unsupplied write permission, using an invalid mutable mode, or accessing an operation's ended temporary loan after resume |
| **`E0521`** | `DestructureMutabilityLaunderingError` | Pattern binding attempts to upgrade a referenced constituent; independent scalar copies are exempt |
| **`E0522`** | `ContainerMutabilityLaunderingError` | A container operation attempts to grant write permission to an immutable or view constituent |
| **`E0523`** | `MutMutAliasingConflictError` | Overlapping mutable arguments passed to `mut` parameters |
| **`E0524`** | `ReadMutAliasingHazardError` | Mutable argument aliases simultaneous read-only argument |
| **`E0525`** | `SpreadLaunderingError` | Spread attempts to grant write permission to a referenced immutable/view constituent |
| **`E0526`** | `CollectionMutationDuringIterationError` | Structurally changing a collection through any alias during an active `for` iteration |
| **`E0527`** | `UnusedMutableBindingError` | Declared mutable authority is never exercised by a reachable write, invocation, retention, or explicit transfer |
| **`E0528`** | `ReturnMutabilityLaunderingError` | A returned borrowed/external reference is received with permissions not supplied by its source |
| **`E0529`** | `ExcessiveCapabilityAnnotationError` | Concrete definition declares unnecessary capabilities; callable contract upper bounds are exempt |
| **`E0530`** | `IllegalCapabilityCloneImmutError` | Ordinary graph contains a constituent ineligible for cloning or immutable copying, or a resource clone violates its contract |
| **`E0531`** | `ImmutableTargetViewError` | View initializer lacks an admissible stable live origin or conceals a forbidden reassignable origin |
| **`E0532`** | `ReassignableScopedResourceError` | Attempting to declare a scoped resource with reassignable `var`/`var mut` authority |
| **`E0533`** | `AliasedNarrowingHazardError` | A live refinement can be invalidated by an overlapping writer during its use |
| **`E0534`** | `HazardErasureProhibitedError` | Callable contract erases actual obligations or a concrete definition uses &closure to conceal direct state |
| **`E0535`** | `NonImmutableBindingError` | Live data, an active environment, or surviving writers prevent immutable publication |
| **`E0536`** | `NonImmutableDeriveInputError` | derive input is live, writable, or an opaque resource rather than immutable ordinary data |
| **`E0537`** | `LiveSliceInvalidationError` | Changing a backing collection's structure while a live slice window or alias may still be used |
| **`E0538`** | `InvalidStateSourceGroupError` | A source group has no capture item, a wrong global/capture kind or owner, an omitted required named ancestor, or bindings from different capture layers |
| **`E0539`** | `InvalidStateContractReferenceError` | A function state reference is used outside an ordinary named definition or does not name a visible ordinary named Ril function provider |
| **`E0601`** | `CrossThreadDataRaceHazardError` | Mutable/live ordinary data or a non-transferable active resource crosses a task boundary |
| **`E0602`** | `IllegalChannelPayloadCapabilityError` | Channel payload is neither immutable ordinary data nor an explicitly detached resource descriptor |
| **`E0603`** | `ChannelEndpointAliasingConflictError` | Endpoint/ticket authority is aliased across tasks, duplicated, or used after close/transfer |
| **`E0604`** | `ScopedResourceEscapeError` | Scoped resource authority escapes its owning lexical block |
| **`E0605`** | `InvalidParallelCapabilityError` | Pure parallel callback has outside mutable/live/resource access or non-local cleanup obligations |
| **`E0606`** | `ScopedTaskEscapeError` | Scope/task/channel authority escapes its owner or violates task confinement |
| **`E0607`** | `DerivedProxyEscapeError` | Draft or draft-derived reference escapes its recipe before immutable publication |
| **`E0610`** | `DuplicateResumeInvocationError` | Invoking affine one-shot resumption `resume` more than once |
| **`E0611`** | `EscapingResumeError` | Escaping resumption handle beyond handler arm lexical scope |
| **`E0612`** | `UnhandledEffectError` | Invoking effect operation without in-scope handler or declaring effect in callable signature |
| **`E0613`** | `ValueEffectAnnotationError` | Attaching algebraic effect annotation ('@Eff') to a non-callable type expression or value binding |
| **`E0614`** | `UnstableHandlerCaptureError` | Retained handler cannot provide a stable legal environment, compatible answer type, or fresh boundary |
| **`E0615`** | `CrossTaskUnhandledEffectError` | Residual effects violate a boundary contract, or an ancestor active handler crosses a task boundary |
| **`E0616`** | `ScopedCleanupEffectError` | Resource cleanup handler (`on_close`) declares or invokes unhandled algebraic effects |
| **`E0617`** | `ScopedCleanupDivergenceError` | Resource cleanup handler (`on_close`) declares or invokes divergent operations (`@Div`) |
| **`E0618`** | `UndischargedLocalEffectError` | Local algebraic effect declared in 'where' is not completely discharged within enclosing block |
| **`E0619`** | `ParallelDisjointAccessConflictError` | Parallel write/read or write/write regions overlap or cannot be proved disjoint |
| **`E0620`** | `PseudoEffectAnnotationError` | Attaching non-effect evaluation strategy (such as '@Parallel') as an algebraic effect annotation |
| **`E0701`** | `ChainedAssignmentProhibitedError` | Chaining assignments (`a = b = c`) |
| **`E0702`** | `InvalidWhereItemError` | Declaring variable binding or non-hoistable item in `where` clause |
| **`E0703`** | `IllegalSequentialDeclarationError` | Declaring 'fn', 'type', or 'eff' in sequential statement stream instead of 'where' clause |
| **`E0704`** | `InvalidSignatureWhereItemError` | Declaring 'fn' or 'eff' in signature 'where' clause (signature where is restricted to 'type') |
| **`E0705`** | `DownwardScopeReferenceError` | Signature 'where' clause references item declared in inner block 'where' clause |
| **`E0706`** | `SignatureTypeNotInWaistWhereError` | Function signature references type declared in block 'where' clause instead of signature 'where' clause |
| **`E0707`** | `InvalidControlTransferContextError` | Using last/next without an enclosing loop or return across a prohibited boundary |
| **`E0710`** | `IllegalControlTransferInFallbackError` | Direct return/last/next transfer out of a fallback expression |
| **`E0711`** | `InvalidResultFallbackError` | Supplying raw value fallback for `Result` without error closure |
| **`E0720`** | `UnusedFallibleResultError` | A fallible result is abandoned without inspection, including through aggregates, tasks, or channel queues |
| **`E0810`** | `CallFamilyViolationError` | Crossing disjoint runtime `fn` and compile-time `meta`/`type` call families |
| **`E0811`** | `CompileTimeBudgetExceededError` | Exhausting evaluation step budget in meta/type functions |
| **`E0812`** | `MetaTypeReturnProhibitedError` | 'meta fn' attempting to return 'type<...>' or sort 'Type'; type construction is monopolized by type functions |
| **`E0813`** | `MetaComputationAnnotationError` | Declaring algebraic effects ('@Eff') or state capabilities ('&Cap') on a 'meta fn' signature |
| **`E0820`** | `TotalityViolationError` | A halt function/type body has uncertified local recursion/iteration or a transitive Div obligation |
| **`E0830`** | `MetaAssertionFailedError` | An assert condition evaluates to false during meta/type evaluation |
| **`E0831`** | `StaticEvaluationPanicError` | A non-assertion panic occurs during meta/type evaluation |
| **`E0901`** | `BodyInDeclModuleError` | Supplying an implementation body, variable initializer, or mutable binding in a '.d.ril' declaration unit |
| **`E0902`** | `MissingBodyInStandardModuleError` | Omitting an implementation body from a function declared in a standard '.ril' module |
| **`E0907`** | `ForeignStructuralFieldPenetrationError` | Attempting to access fields, mutate, index, deconstruct, or instantiate an opaque external type |
| **`E0908`** | `UnsupportedExternalAuthorityContractError` | External declaration or use requests authority outside ordinary exchange, temporary callbacks, and explicitly listed resource contracts |
