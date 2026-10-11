# The Ril Language Specification

**Version:** 0.1.0  
**Status:** Canonical Reference Specification  
**Format:** Code-First Normative Document  

---


## Document Conventions

- **Normative Invariants**: Language guarantees and type safety rules are formally declared under titled normative invariants. All conforming Ril implementations must enforce these invariants unconditionally.
- **Grammar Productions**: Syntactic grammar is formally specified in Extended Backus-Naur Form (EBNF).
- **Normative Code Annotations**: Code examples throughout this specification serve as executable verification tests:
  - `-- OK`: Syntactically and semantically valid Ril programs.
  - `-- Error [EXXXX]`: Programs that must be statically rejected by the compiler with the indicated diagnostic error code.
  - `-- Panics`: Programs that raise deterministic runtime panics under defect conditions.
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
  - [Functional Updates via Derive](#functional-updates-via-derive)
  - [Generic Parameters, Defaults, and Value Sorts](#generic-parameters-defaults-and-value-sorts)
  - [Tripartite Ontology and Type Definition Boundaries](#tripartite-ontology-and-type-definition-boundaries)
- [Declarations and Bindings](#declarations-and-bindings)
  - [Three-Tier Mutability Architecture and Storage Matrix](#three-tier-mutability-architecture-and-storage-matrix)
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
  - [Parameter Modes, Caller Obligations, and Defaults](#parameter-modes-caller-obligations-and-defaults)
  - [Anonymous Functions, Trailing Closures, and Projection Accessors](#anonymous-functions-trailing-closures-and-projection-accessors)
  - [Closures, Factory Signatures, and Lexical Environments](#closures-factory-signatures-and-lexical-environments)
  - [Higher-Order Functions and Capability Forwarding](#higher-order-functions-and-capability-forwarding)
- [State and Capability Tracking](#state-and-capability-tracking)
  - [Local Mutation Purity and Local Capability Discharge](#local-mutation-purity-and-local-capability-discharge)
  - [Parameter Mutation](#parameter-mutation)
  - [Retained Mutable Sharing](#retained-mutable-sharing)
  - [External State Tracking](#external-state-tracking)
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

Whitespace (spaces, tabs, newlines) separates tokens. Semicolons `;` are optional expression separators. The final expression in a block without a semicolon serves as the block's return value. Newlines act as statement terminators unless an expression continuation operator (`+`, `-`, `*`, `|>` etc.) indicates ongoing evaluation.

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

### Identifiers and Casing Invariants

```ebnf
Identifier         ::= PascalCase | SnakeCase | ScreamingSnakeCase | SuppressedVar
PascalCase         ::= [A-Z] { [a-zA-Z0-9] }
SnakeCase          ::= [a-z] [a-z0-9]* { "_" [a-z0-9]+ }
ScreamingSnakeCase ::= [A-Z] [A-Z0-9]* { "_" [A-Z0-9]+ }
SuppressedVar      ::= "_" [a-z] [a-z0-9]* { "_" [a-z0-9]+ }
Wildcard           ::= "_"
```

Identifiers are strictly partitioned at the lexer and parser levels across grammatical roles under the **Closed Casing Invariant**:

- **`PascalCase`**: Strictly reserved for types (`type`), ADT variant constructors, nominal wrappers, algebraic effects (`eff`), generic type parameters (`T`, `ItemType`), and module namespace identifiers (`Array`, `Channel`, `Geometry`).
   - **Acronym Title-Casing Rule**: Acronyms within `PascalCase` MUST be title-cased as regular words (`HttpServer`, `UserId`, `JsonParser`, NOT `HTTPServer`, `UserID`, `JSONParser`) (`E0102`).
- **`snake_case`**: Strictly used for runtime variables (local bindings, function parameters, reassignable variables `var`, and pinned mutable handles `let mut`), const generic parameters (`cap: int`), named functions (`fn`, `meta fn`), record fields, and module path segments (`ril/array`, `math/geometry`).
- **`SCREAMING_SNAKE_CASE`**: Strictly reserved for compile-time constants (`meta let`) and top-level immutable constants (`let`). Top-level mutable variables (`var`, `let mut`) MUST use `snake_case`.
- **Wildcard & Suppression**: A single underscore `_` is strictly the wildcard discard pattern, not an identifier (`E0322`). An identifier with a leading underscore `_snake_case` declares an intentionally unused variable or parameter, suppressing unused binding diagnostics (`E0527`).

```ril
-- PascalCase: Types, Constructors, Effects, and Generic Parameters
type UserAccount = { id: int }         -- OK: type identifier
type Result<T, E = str> { Ok(T), Err(E) } -- OK: generic parameters and constructors
eff FileIo { read() -> str }           -- OK: effect identifier
type HttpServerConfig = { port: int }  -- OK: title-cased acronym

-- snake_case: Variables (local, param, top-level var / let mut), Functions, and Fields
let user_count = 10                    -- OK: local variable identifier
var total_score = 0                    -- OK: local reassignable variable
var active_workers = 0                 -- OK: top-level reassignable mutable variable
fn compute_area(width: f64) -> f64 { width * 2.0 } -- OK: function identifier
meta fn pad_align(size: int) -> int { size }       -- OK: compile-time function

-- SCREAMING_SNAKE_CASE: meta let and Top-Level Immutable Variables ONLY
meta let MAX_BUFFER_SIZE = 1024 * 64   -- OK: compile-time constant
let DEFAULT_TIMEOUT_MS = 5000          -- OK: top-level immutable constant

-- Wildcard and Unused Suppression
let _ = user_count                     -- OK: wildcard discard
fn on_event(ev: Event, _ctx: Context) { handle(ev) } -- OK: '_ctx' suppresses unused warning

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

The following 34 tokens are strictly reserved keywords:

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
-- Reserved keywords in action:
pub opaque type Token = int            -- 'pub', 'opaque', 'type'
meta let COMPILE_ID = 101              -- 'meta', 'let'
eff Logger { log(str) -> () }          -- 'eff'
use ril/array::{push}                  -- 'use'
halt fn total_step() -> bool { true }  -- 'halt', 'true', 'fn'
fn manage_resource() -> Result<(), IoError> {
    let scoped res = File::open("a.txt")?  -- 'scoped', '?' inside function frame
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
DecimalLiteral ::= Digit { [ "_" ] Digit } [ IntSuffix ]
HexLiteral     ::= "0" ( "x" | "X" ) HexDigit { [ "_" ] HexDigit } [ IntSuffix ]
OctalLiteral   ::= "0" ( "o" | "O" ) OctalDigit { [ "_" ] OctalDigit } [ IntSuffix ]
BinaryLiteral  ::= "0" ( "b" | "B" ) BinaryDigit { [ "_" ] BinaryDigit } [ IntSuffix ]
IntSuffix      ::= "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64" | "int" | "bigint"
FloatLiteral   ::= Digit { [ "_" ] Digit } "." Digit { [ "_" ] Digit } [ Exponent ] [ FloatSuffix ]
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
```

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

Records are structural collections of named fields. Closed records do not support width subtyping. Field access on records is strictly compile-time identifier dot-access (`r.field`); dynamic string indexing (e.g. `r["key"]` or `r.("key")`) is prohibited. In symmetry, type-level field extraction uses dot projection (`User.id` or computed projection `T.(K)`); bracket indexing on record types (e.g. `User["id"]`) is prohibited (`E0324`).

Named row tail polymorphism (`..R`) allows generic functions to accept and preserve additional caller fields across pipelines. Pattern destructuring with `..rest` extracts a concrete, statically typed sub-record containing the remaining known fields.

```ebnf
RecordType     ::= "{" [ RecordField { "," RecordField } [ "," ] [ ".." Identifier ] ] "}"
RecordField    ::= [ "mut" ] Identifier ":" TypeExpression
TypeProjection ::= PrimaryType "." ( Identifier | TupleIndex | "(" Expression ")" )
TupleIndex     ::= Digit { Digit }
```

```ril
type User = { id: int, name: str }
let u: User = .{ id: 1, name: "Alice" } -- OK: exact closed record match

-- Closed record rejects unexpected fields (E0302):
-- let bad_u: User = .{ id: 1, name: "Alice", age: 30 } -- Error [E0302]: UnexpectedFieldError: unexpected field 'age' in closed record 'User'

-- Field access is strictly compile-time identifier dot-access:
let user_id = u.id                     -- OK: direct static offset lookup
-- let bad_index = u["name"]           -- Error [E0324]: DynamicRecordIndexProhibitedError: records do not support dynamic index lookup
-- let bad_accessor = u.("name")       -- Error [E0324]: DynamicRecordIndexProhibitedError: dynamic string accessor prohibited

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
TupleType   ::= "(" TypeExpression "," { TypeExpression "," } [ TypeExpression ] ")"
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
VariantDecl         ::= Identifier [ GenericParams ]
                        [ "(" VariantFields ")" | "{" RecordVariantFields "}" ] [ "->" TypeExpression ]
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
fn eval_int(e: Expr<int>) -> int {
    match e {
        LitInt(n) -> n,
        Add(a, b) -> eval_int(a) + eval_int(b),
        -- LitBool(b) -> 0             -- Error [E0304]: UnreachableMatchArmError: unreachable match arm: constructor 'LitBool' binds T = bool, incompatible with Expr<int>
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

#### Constructor-Tuple Equivalence Invariant

Data constructors (algebraic sum type variants and nominal type wrappers) establish a definitional equivalence between comma-separated multi-field declarations and single-tuple payloads:
$$\text{Variant}(T_1, T_2, \dots, T_n) \equiv \text{Variant}((T_1, T_2, \dots, T_n)) \quad (n \ge 0)$$

Ril strictly possesses no 1-element tuples `(T,)` (`(x)` denotes parenthesized grouping; tuples require $\ge 2$ elements; `()` denotes unit). Constructor arity $n$ in expressions and patterns is strictly deterministic:
- **Scope Restriction (Strict Constructor Boundary)**: Equivalence is confined strictly to Data Constructors. Ordinary functions (`fn`), closures, and methods maintain strictly separate parameter lists and register ABIs (`E0301`).
- **Positional Tuple Expansion & Literal Compatibility ($n \ge 2$)**: In expression construction and pattern matching, $C(e_1, \dots, e_n)$ and explicit tuple literals $C((e_1, \dots, e_n))$ are definitionally equivalent: outer constructor parentheses absorb inner tuple parentheses.
- **Whole-Tuple Binding or Single Argument ($n = 1$)**: $C(val)$ constructs or matches the scalar payload or whole-tuple object.
- **Unit Payload Constructor ($n = 0$)**: When a variant's payload type is `()`, $C()$ constructs or matches the unit payload directly ($C() \equiv C(())$ ). Bare constructor identifiers without parentheses (e.g. bare `Ok`) are strictly first-class constructor functions (`fn(T) -> Result<T, E>`), and cannot be evaluated as values without `()` (`E0301`).
- **Nullary Variant Tag Invariant**: Variants declared without a payload (e.g. `None` in `type Option<T> { Some(T), None }`) are pure zero-field tags: they MUST be written without parentheses (`None`). Supplying argument parentheses to a nullary variant (`None()`) is statically rejected (`E0301`).
- **Non-Transitivity (Single-Layer Invariant)**: Equivalence applies strictly to the outermost constructor argument boundary. Nested tuples (e.g. `Variant((A, B), C)`) require explicit grouping and do NOT flatten recursively (`Variant(a, b, c)` is rejected with `E0301`).
- **Rigid Type Variable Invariant**: Deconstructing $C(p_1, \dots, p_n)$ ($n \ge 2$) against an unconstrained generic type parameter $T$ is statically rejected with `E0301`.
- **First-Class Constructor Canonical Type**: A constructor $C$ carrying a tuple payload $(T_1, \dots, T_n)$ possesses the canonical unary first-class callable type $\text{fn}((T_1, \dots, T_n)) \to S$. In Check Mode expecting a multi-parameter callable ($\Gamma \vdash C \Leftarrow \text{fn}(T_1, \dots, T_n) \to S$), context-directed $\eta$-expansion ($\backslash x_1, \dots, x_n \to C(x_1, \dots, x_n)$ ) applies.

```ril
-- Result construction and matching with unit payload (n = 0):
let unit_res: Result<(), str> = Ok()             -- OK: n = 0 constructs () payload directly
let auto_unit = Ok()                             -- OK: synthesizes Result<(), _> (payload is ())
-- let bad_bare = Ok                             -- Error [E0301]: TypeMismatchError: 'Ok' is a constructor function; write 'Ok()' to construct Result<(), _>

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
let res_from_pair = Ok(pair)                     -- OK: n = 1 passes existing tuple
let res_compat = Ok((200, "OK"))                 -- OK: n = 1 explicit tuple literal

match res {
    Ok(code, msg) -> println(msg),               -- OK: n = 2 directly unpacks tuple elements
    Ok(p) -> println(p.1),                       -- OK: n = 1 binds entire tuple to 'p'
    Err(e) -> println(e),
}

-- Multi-field variant declaration and tuple equivalence:
type Geometry {
    TwoPoints(int, int),                         -- Equivalent to TwoPoints((int, int))
}

let p1 = TwoPoints(10, 20)                       -- OK: positional elements
let p2 = TwoPoints(pair)                         -- OK: passing existing tuple variable
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
NominalDecl ::= [ "pub" ] "type" Identifier [ GenericParams ] [ "(" TypeExpression ")" ] [ WhereClause ]
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
-- let bad = UserId                    -- Error [E0314]: ArityMismatchError: nominal wrapper 'UserId' requires 1 argument, found 0
```

### Deep Immutability

`clone_immut(x)` deeply normalizes an object graph into an immutable value `Immut<T>`, guaranteeing permanent immunity to data races and mutation across threads.

```ril
type Document = { mut title: str, mut tags: []str }

let mut doc = Document.{ title: "Draft", tags: ["ril", "spec"] }
let frozen: Immut<Document> = clone_immut(doc)

-- Direct mutation on Immut<T> is rejected:
-- frozen.title = "Published"          -- Error [E0520]: MutabilityLaunderingError: cannot mutate field 'title' through permanently immutable 'Immut<Document>'

-- Laundering Immut<T> into a mutable parameter is rejected:
fn modify_doc(mut d: Document) { d.title = "Changed" }
-- modify_doc(mut frozen)              -- Error [E0520]: MutabilityLaunderingError: cannot borrow permanently immutable 'Immut<Document>' as 'mut'

let mut independent_copy = clone(doc)  -- OK: deep mutable clone
independent_copy.title = "Published"   -- OK: independent copy is mutable
```

### Type Identity and Subtyping

- **Width Subtyping**: Rejected on closed records. Permitted only via open row parameters (`{ id: int, .. }`).
- **Depth Subtyping**: Mutable fields are invariant. Read-only fields are covariant.
- **Callable Subtyping**: Parameters are contravariant; return types are covariant. State capabilities are covariant across the capability lattice (`&mut` $\sqsubset$ `&^mut`).

```ril
type Animal = { name: str }
type Dog = { name: str, breed: str }

-- Covariant read-only return:
type Getter<T> = fn() -> T
-- fn(d: Dog) -> Dog is a valid subtype of fn(d: Dog) -> Animal
```

### Memory Model and Handle Invariants

- **Handle-Level Immutability Invariant**: A binding declared with `let` establishes a completely immutable handle (neither reassignment nor in-place interior mutation is permitted).
- **Pinned Mutable Handles (`let mut`)**: A binding declared with `let mut` establishes a pinned mutable handle over reference types. It permits in-place mutation of fields and elements, but statically rejects handle reassignment (`E0502`). Binding value types to `let mut` is statically rejected (`E0402`).
- **Reassignable Mutable Variables (`var`)**: A binding declared with `var` establishes a reassignable mutable variable cell, permitting both slot reassignment and interior field mutation.
- **Live Views (`let view x = obj`)**: A live view strips write permissions locally but dynamically observes concurrent or subsequent mutations on the underlying heap object. The target MUST be a pinned mutable root (`let mut` handle or `mut` parameter).
- **Definite Mutation Invariant (`E0527`)**: Any binding declared with `let mut` or `var`, or parameter declared with `mut`, MUST undergo at least one reachable write operation along an executable path (`let mut` requires in-place mutation; `var` requires reassignment or mutation).

```ril
type Counter = { mut count: int }
let mut original = Counter.{ count: 0 }

let view v = original                  -- Live view into pinned root 'original'
-- v.count = 5                         -- Error [E0520]: MutabilityLaunderingError: cannot mutate field 'count' through read-only view 'v'

original.count += 1
let observed = v.count                 -- observed is 1 (live view reflects mutation)

-- Pinned handle reassignment rejected:
-- original = Counter.{ count: 10 }    -- Error [E0502]: PinnedHandleReassignmentError: cannot reassign pinned mutable handle 'original'; use 'var'

-- Value type declared let mut rejected:
-- let mut bad_scalar = 42             -- Error [E0402]: ValueTypePinnedMutError: value type 'int' has no interior mutability; use 'var'

-- Definite Mutation Invariant:
-- let mut unused_mut = Counter.{ count: 0 } -- Error [E0527]: UnusedMutableBindingError: variable 'unused_mut' declared 'let mut' but never modified in-place
-- var unused_var = 10                 -- Error [E0527]: UnusedMutableBindingError: variable 'unused_var' declared 'var' but never modified or reassigned
```

### Functional Updates via Derive

**`derive(base, recipe)`**: Executes deep functional updates over reference data graphs via path-wise copy-on-write (structural sharing) mechanics. The mutating closure `recipe` mutates a derived proxy `next` in place, returning a fresh, unaliased immutable object without modifying `base`. Unmodified subtrees preserve pointer identity with `base`. Derived proxies cannot escape the recipe closure via return, external assignment, or closure publication (`E0607`).

#### Normative Rules for Functional Updates
- **Transactional Abort-Safety Invariant**: `derive` provides all-or-nothing transactional derivation. If `recipe` terminates abnormally via delimited early abort ([Affine Resumption and Delimited Early Abort](#affine-resumption-and-delimited-early-abort)) or runtime panic ([Failure Model and Error Categories](#failure-model-and-error-categories)):
   - `base` remains completely unmodified and structurally intact.
   - The in-flight derived proxy `next` and uncommitted path-copied nodes are discarded during stack frame unwinding without publishing a derived value, becoming unreachable garbage collected by tracing GC.
- **Preservation of Commit-on-Write**: Ambient physical mutations to external memory performed by `recipe` prior to an abort remain permanently committed ([Affine Resumption and Delimited Early Abort](#affine-resumption-and-delimited-early-abort)) and are never rolled back.
- **Derived Proxy Confinement (`E0607`)**: Derived proxies cannot escape the `recipe` closure via return value, external variable assignment, or closure publication (`E0607: DerivedProxyEscapeError`).

```ril
type UserSettings = { mut theme: str, mut notifications: bool }
type UserProfile = { mut name: str, mut settings: UserSettings }

let u1 = UserProfile.{
    name: "Alice",
    settings: UserSettings.{ theme: "dark", notifications: true },
}

-- Normal derivation via path-wise copy-on-write:
let u2 = u1 |> derive \mut next -> {
    next.settings.theme = "light"
}
assert(u1.settings.theme == "dark")     -- u1 remains unchanged
assert(u2.settings.theme == "light")    -- u2 is a fresh updated copy
assert(u1.settings != u2.settings)      -- Modified subtree gets a fresh copy

-- Transactional Abort-Safety: Delimited Early Abort (Affine Resumption)
eff Auth {
    check() -> bool,
}

let mut audit_log: []str = []
let abort_result = {
    with Auth::check() -> "ABORTED"     -- Handler aborts early without resume
    u1 |> derive \mut next -> {
        audit_log !> Array::push("RECIPE_START") -- Physical mutation committed
        next.settings.theme = "solarized"        -- Path-wise CoW proxy modified
        Auth::check()                            -- Delimited early abort triggered
        next.name = "Bob"                        -- Unreachable
    }
}
assert(abort_result == "ABORTED")
assert(u1.settings.theme == "dark")              -- base is strictly unmodified
assert(u1.name == "Alice")
-- Commit-on-Write invariant: external mutations performed prior to abort stay committed:
assert(audit_log == ["RECIPE_START"])

-- Transactional Abort-Safety: Runtime Panic (Failure Model)
use ril/concurrent::{scope, TaskFault}

let panic_result: Result<UserProfile, TaskFault> = scope \mut s -> {
    s.fork \-> {
        u1 |> derive \mut next -> {
            next.settings.theme = "contrast"
            let zero = 0
            let _ = 10 / zero                    -- Panics: division by zero
            next.name = "Charlie"
        }
    }
}
-- panic_result evaluates to Err(TaskFault::Panicked(...))
assert(u1.settings.theme == "dark")              -- base remains pristine

-- Derived proxy escape is strictly rejected:
-- let esc1 = u1 |> derive \mut next -> next     -- Error [E0607]: DerivedProxyEscapeError: derived proxy cannot escape 'derive' closure
-- let mut leaked = ()
-- u1 |> derive \mut next -> { leaked = next }   -- Error [E0607]: DerivedProxyEscapeError: derived proxy cannot escape 'derive' closure
```

### Generic Parameters, Defaults, and Value Sorts

Generic parameters parameterize data type declarations (`type`, `pub type`), nominal wrappers, and algebraic sum types. Parameters are partitioned into **Type Parameters** (of sort `Type` or higher-kinded `Type -> Type`) and **Const Value Parameters** (`name: ValueType`).

```ebnf
GenericParams         ::= "<" GenericParamDecl { "," GenericParamDecl } [ "," ] ">"
GenericParamDecl      ::= TypeParamDecl | ConstParamDecl
TypeParamDecl         ::= PascalCase [ ":" TypeSort ] [ "=" TypeExpression ]
ConstParamDecl        ::= SnakeCase ":" ValueType [ "=" Expression ]
TypeSort              ::= "Type" | KindSignature | RecordConstraint | KeyofConstraint
KindSignature         ::= "Type" "->" ( "Type" | KindSignature )
RecordConstraint      ::= "{" [ RecordConstraintField { "," RecordConstraintField } [ "," ] ] ".." Identifier "}"
RecordConstraintField ::= [ "mut" ] Identifier ":" TypeExpression
KeyofConstraint       ::= "keyof" TypeExpression
GenericArgs           ::= "<" GenericArg { "," GenericArg } [ "," ] ">"
GenericArg            ::= TypeExpression | Expression
```

- **Trailing Defaults Invariant (`E0316`)**: If a generic parameter declares a default argument (`= Default`), all subsequent generic parameters in the same parameter list MUST declare default arguments.
- **Telescopic Left-to-Right Scoping Invariant (`E0320`)**: A default argument expression $D_i$ may reference generic parameters declared to its left ($X_1, \dots, X_{i-1}$). Forward references and direct/indirect circular dependencies are statically rejected (`E0320`).
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
|  - Value vs Reference types         |  - Three-tier mutability            |  - Algebraic effects ('eff')        |
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
   - **Metaphysical Nature**: Memory representation, data alignment, structural topology, and nominal identity of values in *normal form* (quiescent data at rest).
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
   - **Metaphysical Nature**: Static tracking of heap mutation authority, storage cell access rights, pointer stability, and aliasing exclusivity. It specifies what memory an activation frame or handle is permitted to mutate, reassign, or retain.
   - **Syntactic Locus**: Variable bindings (`let`, `let mut`, `var`, `let view`), function parameter modes (`p: T`, `mut p: T`), and callable capability qualifiers (`&mut`, `&^mut`, `&closure`, `&capture`, `&{ident}`, `&{mut ident}`).
   - **Guarantees**: Governed by the Law of Exclusivity, Monotonic Permission Degradation, and Anti-Laundering theorems (`E0520`–`E0528`), preventing hidden aliasing, pointer invalidation, and data races without marker traits or lifetime annotations.
   - **Axiom of Non-Reification**: Capabilities are operational permissions, not data values. A capability cannot be instantiated at runtime, bound to a variable, stored in a collection, or aliased as a standalone type.

- **Domain III: Control & Transfer Domain ($\mathcal{E}$)**:
   - **Metaphysical Nature**: Dynamic control inversion, delimited continuation interception, stack unwinding protocols, and cooperative fiber scheduling. It specifies what non-local control transfers and ambient runtime requests can occur during expression reduction.
   - **Syntactic Locus**: Exclusively confined to computation / arrow signatures (`fn(P) -> R @Eff &Cap`), effect declarations (`eff`), and handler blocks (`with`).
   - **Constituents**:
     - *Algebraic Effect Definitions*: `eff FileIo { read() -> str }`.
     - *Stack Handlers*: `with Handler { op(args) -> ... }`.
     - *Affine Resumptions*: `resume value`.
     - *Built-in Effect Sub-Lattice*: `@Fiber` (cooperative leaf I/O quantum) $\subset$ `@Async` (compound concurrency alias) $\equiv \lbrace\text{Fiber}, \text{Concurrent}\rbrace$, disjoint from `@Div` (divergence).
   - **Axiom of Delimited Execution**: Effects represent active computational protocols between code and ambient stack handlers. Once an expression is reduced to normal form, its effects have transpired; evaluated values carry zero latent effects.

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
fn get_field<T, K: keyof T>(record: T, key: K) -> T.(K) {
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
Variable bindings serve as access portals to physical storage locations in registers, stack frames, and the GC heap. Memory is spatial, persistent, and subject to aliasing relationships. Consequently, static capability tracking governs:
- **Reassignment Privilege**: Whether a binding slot can be overwritten (`var` vs `let` / `let mut`).
- **Interior Write Privilege**: Whether fields reachable through a handle can be mutated in place (`let mut` / `var` vs `let` / `let view`).
- **Live Observation**: Whether a handle dynamically observes background mutations of an aliased heap object (`let view`).
- **Anti-Laundering Degradation**: Enforcing monotonic permission degradation ($\text{Mut} \succ \text{ReadOnly} \succ \text{None}$) across destructuring patterns, container insertions, and returns (`E0520`–`E0528`).

##### Algebraic Effects Never Govern Bindings (Function & Data Colorlessness)
Algebraic effects govern dynamic, non-local control transfers during expression evaluation:
- When an effectful operation is evaluated (`Console::print("hi")`, `Yield::emit(x)`), it traverses up the dynamic execution stack to find an active enclosing `with` handler.
- Upon reduction to normal form, all effect operations have already been dispatched and handled.
- The resulting value is an inert memory representation in normal form, carrying Shape and Access permissions, but **zero latent effects**.
- Value bindings, record fields, tuple components, and array elements are strictly colorless. Decorating value bindings with `@Eff` triggers `E0613: ValueEffectAnnotationError`.

##### The Intersecting Boundary: Capability-Bearing Effect Operations
The tripartite domains intersect cleanly in capability-bearing effect operations, where control routing and memory mutation rights are orthogonal:

```ril
eff BufferIO {
    read_into(mut buf: []u8) -> int &mut,       -- Operation demands in-place buffer mutation
}
```
- The effect tag `BufferIO` governs **Control** (Domain III: who intercepts the operation up the call stack).
- The capability annotation `&mut` governs **Access** (Domain II: the operation demands write authority into caller-supplied storage).

#### Tripartite EBNF Grammar Formalization

```ebnf
(* ========================================================================= *)
(* 1. TYPE EXPRESSIONS (Domain I: Data & Shape)                              *)
(* ========================================================================= *)

TypeDecl         ::= [ "pub" ] [ "halt" ] "type" PascalCase [ GenericParams ] [ WhereClause ] "=" TypeExpression
OpaqueTypeDecl   ::= [ "pub" ] "opaque" "type" PascalCase [ GenericParams ] [ WhereClause ] "=" TypeExpression
NominalDecl      ::= [ "pub" ] "type" PascalCase [ GenericParams ] [ "(" TypeExpression ")" ] [ WhereClause ]
SumTypeDecl      ::= [ "pub" ] "type" PascalCase [ GenericParams ] [ WhereClause ] "{" VariantDeclList "}"

TypeExpression   ::= PrimaryType
                   | RecordType
                   | TupleType
                   | ArrayType
                   | MapType
                   | CallableType
                   | TypeProjection
                   | TypeFunctionExpr

PrimaryType      ::= PrimitiveType | NominalRef | "(" TypeExpression ")"
NominalRef       ::= PascalCase [ GenericArgs ]
ArrayType        ::= "[" [ Expression ] "]" TypeExpression
MapType          ::= "[" TypeExpression ":" TypeExpression "]"
TupleType        ::= "(" TypeExpression "," { TypeExpression "," } [ TypeExpression ] ")"

(* Callable Type: THE COMPUTATION CONFLUENCE POINT *)
CallableType     ::= "fn" "(" [ ParameterTypeList ] ")" [ "->" TypeExpression ] [ EffectAnnot ] [ StateAnnot ]
ParameterTypeList::= ParameterTypeItem { "," ParameterTypeItem } [ "," ]
ParameterTypeItem::= [ "mut" ] [ SnakeCase ":" ] TypeExpression

(* Records: 'mut' is exclusively an interior field layout marker *)
RecordType       ::= "{" [ RecordFieldList ] "}"
RecordFieldList  ::= RecordField { "," RecordField } [ "," ] [ ".." SnakeCase ]
RecordField      ::= [ "mut" ] SnakeCase ":" TypeExpression

(* Sum Types: Variants are pure data constructors *)
VariantDeclList  ::= VariantDecl { "," VariantDecl } [ "," ]
VariantDecl      ::= PascalCase [ GenericParams ] [ VariantPayload ] [ "->" TypeExpression ]
VariantPayload   ::= "(" VariantFields ")" | "{" RecordFieldList "}"
VariantFields    ::= VariantField { "," VariantField } [ "," ]
VariantField     ::= [ SnakeCase ":" ] TypeExpression

(* Generic Parameters: Strictly Types or Const Values *)
GenericParams    ::= "<" GenericParamDecl { "," GenericParamDecl } [ "," ] ">"
GenericParamDecl ::= TypeParamDecl | ConstParamDecl
TypeParamDecl    ::= PascalCase [ ":" TypeSort ] [ "=" TypeExpression ]
ConstParamDecl   ::= SnakeCase ":" ValueType [ "=" Expression ]
TypeSort         ::= "Type" | KindSignature | RecordConstraint | KeyofConstraint
KindSignature    ::= "Type" "->" ( "Type" | KindSignature )
RecordConstraint ::= "{" [ RecordConstraintField { "," RecordConstraintField } [ "," ] ] ".." SnakeCase "}"
RecordConstraintField ::= [ "mut" ] SnakeCase ":" TypeExpression
KeyofConstraint  ::= "keyof" TypeExpression

(* ========================================================================= *)
(* 2. CONTROL & TRANSFER DOMAIN (Domain III: Algebraic Effects)              *)
(* ========================================================================= *)

EffectDecl       ::= [ "pub" ] "eff" PascalCase [ GenericParams ] "{" EffectMemberList "}"
EffectMemberList ::= ( EffectOpDecl { "," EffectOpDecl } [ "," ] )
                   | ( PascalCase { "," PascalCase } [ "," ] )
EffectOpDecl     ::= SnakeCase "(" [ ParameterList ] ")" [ "->" TypeExpression ] [ StateAnnot ]
EffectAnnot      ::= "@" EffectRow
EffectRow        ::= EffectIdentifier { "+" EffectIdentifier }
EffectIdentifier ::= PascalCase [ GenericArgs ]

(* ========================================================================= *)
(* 3. STORAGE & ACCESS DOMAIN (Domain II: Capabilities)                      *)
(* ========================================================================= *)

StateAnnot       ::= StateCapability { StateCapability }
StateCapability  ::= "&mut"
                   | "&^mut"
                   | "&closure"
                   | "&capture"
                   | "&{" [ "^" ] "mut" SnakeCase "}"
                   | "&{" SnakeCase "}"
```

---

## Declarations and Bindings

### Three-Tier Mutability Architecture and Storage Matrix

Ril decomposes storage mutability into a 2×2 matrix, cleanly separating variable slot reassignment from interior heap mutation:

| Binding Form | Variable Reassignment (`x = ...`) | In-Place Mutation (`x.f = ...`, `x !> ...`) | Storage Semantics | Mental Model & Lifetime Invariants |
| :--- | :---: | :---: | :--- | :--- |
| **`let`** | Prohibited (`E0501`) | Prohibited (`E0520`) | **Immutable Binding** | Frozen snapshot, pure scalar copy, constant handle. |
| **`let mut`** | Prohibited (`E0502`) | Permitted (`&mut`) | **Pinned Mutable Handle** | Fixed GC heap allocation; guaranteed pointer stability. |
| **`var`** | Permitted | Permitted (`&mut`) / Prohibited (`E0520` if ReadOnly) | **Reassignable Variable** | Dynamic slot, loop accumulator, reassignable cursor. |
| **`let view`** | Prohibited (`E0501`) | Prohibited (`E0520`) | **Live Read-Only View** | Read-only observation window over a pinned mutable root. |

```ril
type UserDoc = { mut title: str, mut score: int }

-- Immutable Binding ('let'):
let ro_val = 100
let ro_doc = UserDoc.{ title: "Guide", score: 50 }
-- ro_val = 200                         -- Error [E0501]: ImmutableReassignmentError: cannot reassign immutable binding 'ro_val'
-- ro_doc.score = 51                    -- Error [E0520]: MutabilityLaunderingError: cannot mutate field 'score' through read-only handle 'ro_doc'

-- Pinned Mutable Handle ('let mut'):
let mut pinned_doc = UserDoc.{ title: "Draft", score: 0 }
pinned_doc.score = 10                  -- OK: in-place interior mutation permitted
pinned_doc.title = "Published"         -- OK: in-place field write permitted
-- pinned_doc = UserDoc.{ title: "New", score: 0 } -- Error [E0502]: PinnedHandleReassignmentError: cannot reassign pinned mutable handle 'pinned_doc'; use 'var'

-- Reassignable Mutable Variable ('var'):
var counter = 0
counter += 1                           -- OK: reassignable scalar
var cursor_doc = pinned_doc            -- OK: reassignable reference variable
cursor_doc.score = 15                  -- OK: interior mutation permitted
cursor_doc = UserDoc.{ title: "Next", score: 100 } -- OK: handle reassignment permitted

-- Live Read-Only View ('let view'):
let view observer = pinned_doc         -- OK: live view over pinned mutable root
assert(observer.score == 15)           -- OK: reads current state
pinned_doc.score = 20                  -- Mutate via root
assert(observer.score == 20)           -- OK: live view dynamically observes mutation
-- observer.score = 25                 -- Error [E0520]: MutabilityLaunderingError: cannot mutate field 'score' through read-only view 'observer'
```

### Immutable Bindings

```ebnf
LetDecl ::= "let" Pattern [ ":" TypeExpression ] "=" Expression
```

```ril
let x = 10                             -- Immutable integer binding
let (a, b) = (1, 2)                    -- Destructuring tuple binding
-- x = 20                              -- Error [E0501]: ImmutableReassignmentError: cannot reassign immutable binding 'x'

type Config = { capacity: int }
let cfg = Config.{ capacity: 64 }
-- let .{ mut capacity } = cfg         -- Error [E0521]: DestructureMutabilityLaunderingError: cannot destructure read-only record into 'mut' binding
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
-- buf = Buffer.{ items: [] }          -- Error [E0502]: PinnedHandleReassignmentError: cannot reassign pinned mutable handle 'buf'; use 'var' if reassignment is intended

-- Value types under let mut are rejected:
-- let mut count: int = 0              -- Error [E0402]: ValueTypePinnedMutError: value type 'int' has no interior mutability; use 'var'

-- Pattern-level pinned mutable destructuring:
type NodePair = { mut left: Buffer, mut right: Buffer }
let mut pair = NodePair.{ left: Buffer.{ items: [] }, right: Buffer.{ items: [] } }
let .{ mut left, mut right } = pair
left.items !> Array::push(10)          -- OK: 'left' is a pinned mutable handle
-- left = Buffer.{ items: [] }        -- Error [E0502]: PinnedHandleReassignmentError: cannot reassign pinned handle 'left'

-- Definite Mutation Invariant:
-- let mut unused = Buffer.{ items: [] } -- Error [E0527]: UnusedMutableBindingError: variable 'unused' declared 'let mut' but never modified in-place
```

### Reassignable Mutable Variables

A binding declared with `var` establishes a **reassignable mutable variable cell**. It permits both variable slot reassignment (`x = ...`) and, when referencing a mutable object, interior in-place mutation (`x.field = ...`).

#### Normative Rules for Reassignable Variables
- **Dual Permission**: A `var` binding allows both in-place field/element mutation and complete slot reassignment.
- **Monotonic Anti-Laundering Degradation (`E0520`)**:
   - Reassigning a read-only reference into a `var` handle carrying mutable permissions is rejected under `E0520: MutabilityLaunderingError`.
   - When initialized from a read-only root (`var cursor = ro_list`), `var` inherits `ReadOnly` handle capability: slot reassignment is permitted (`cursor = cursor.next`), but interior mutation is statically rejected (`E0520`).
- **Definite Mutation Invariant (`E0527`)**: A variable declared `var` MUST undergo at least one reachable write operation (reassignment or in-place mutation) along an executable path.

```ebnf
VarDecl ::= [ "pub" ] "var" Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
```

```ril
-- Reassignable primitive scalar:
var counter = 0
counter += 1                           -- OK: reassignable scalar
counter = 10                           -- OK: direct reassignment
assert(counter == 10)

-- Fully mutable reference variable:
var active_buf = Buffer.{ items: [1] }
active_buf.items !> Array::push(2)     -- OK: in-place mutation
active_buf = Buffer.{ items: [10, 20] } -- OK: handle reassignment permitted on 'var'
assert(len(active_buf.items) == 2)

-- Read-only cursor over immutable structures:
type Node = { val: int, next: ?Node }
let ro_node2 = Node.{ val: 2, next: None }
let ro_node1 = Node.{ val: 1, next: Some(ro_node2) }

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

Scoped bindings associate resources with lexical scopes. When exiting the enclosing scope (by normal completion, return, or unwinding), the cleanup handler executes in strict Last-In, First-Out (LIFO) order.

#### Normative Rules for Scoped Bindings
- **LIFO Destruction Order**: Scoped cleanups execute in strict reverse declaration order upon exiting the enclosing lexical block.
- **Hermetic Cleanup Invariant (`E0616`, `E0617`)**: The `on_close` cleanup handler associated with `let scoped` MUST be effect-closed ($\mathop{\mathrm{Effects}} = \emptyset$, rejected under `E0616: ScopedCleanupEffectError`) and non-divergent (`@Div` prohibited, rejected under `E0617: ScopedCleanupDivergenceError`).
- **Permitted In-Place Mutation**: In-place mutations on local and external mutable state (`&mut`, `&^mut`) within `on_close` are permitted under Commit-on-Write semantics ([Affine Resumption and Delimited Early Abort](#affine-resumption-and-delimited-early-abort)).
- **Double-Fault Escalation**: If an unhandled panic occurs while executing an `on_close` handler during active stack unwinding (due to prior panic or delimited early abort), the runtime MUST NOT attempt secondary unwinding. In structured concurrency scopes, the task transitions immediately to `TaskFault::DoubleFaultFatal` ([Structured Concurrency and Panic Containment](#structured-concurrency-and-panic-containment)); in unsupervised execution frames, the process terminates immediately with an unrecoverable fatal abort.
- **Prohibition of `var scoped` (`E0532`)**: Scoped resource bindings register cleanups to the enclosing lexical block in strict LIFO order. Reassigning a scoped variable would corrupt runtime block-exit unwinding. Therefore, `var scoped` and `scoped var` are statically prohibited (`E0532: ReassignableScopedResourceError`).

```ebnf
ScopedDecl ::= "let" "scoped" [ "mut" ] Identifier [ ":" TypeExpression ] "=" Expression
```

```ril
type Resource = { name: str, on_close: fn() -> () }

-- Scoped bindings invoke cleanup upon exiting enclosing scope in strict LIFO order:
let mut event_log: []str = []
{
    let scoped first = Resource.{
        name: "R1",
        on_close: \-> event_log !> Array::push("closed_R1")
    }
    -- 'let scoped mut' permits in-place mutation of the pinned scoped handle:
    let scoped mut second = Resource.{
        name: "R2",
        on_close: \-> event_log !> Array::push("closed_R2")
    }
    second.name = "R2_modified"        -- OK: 'second' is declared 'let scoped mut'
    -- second = Resource.{ name: "R3", on_close: \-> () } -- Error [E0502]: PinnedHandleReassignmentError: cannot reassign pinned scoped handle 'second'

    -- Scope exit triggers cleanup in strict LIFO order:
    -- 'second' closes FIRST, 'first' closes SECOND
}
assert(event_log == ["closed_R2", "closed_R1"])

-- Iteration cleanup executes at the end of each iteration:
let mut iter_log: []str = []
for ["A", "B"] as item {
    let scoped res = Resource.{
        name: item,
        on_close: \-> iter_log !> Array::push("closed_" ++ item)
    }
    -- 'res' is cleaned up immediately before the next iteration begins
}
assert(iter_log == ["closed_A", "closed_B"])

-- Static violations:
-- var scoped bad_reassign = Resource.{ name: "Bad", on_close: \-> () } -- Error [E0532]: ReassignableScopedResourceError: scoped resource bindings cannot be declared 'var'
-- let scoped bad_eff = Resource.{ name: "BadEff", on_close: \-> Console::print("leak") } -- Error [E0616]: ScopedCleanupEffectError: scoped cleanup handler cannot declare or invoke unhandled algebraic effects
-- let scoped bad_div = Resource.{ name: "BadDiv", on_close: \-> loop {} } -- Error [E0617]: ScopedCleanupDivergenceError: scoped cleanup handler cannot declare or invoke divergent operations
```

### Live View Bindings

An explicit `let view` binding creates a live read-only observation handle into an existing reference object located on the managed GC heap. It strips write permissions locally while dynamically observing mutations performed through the underlying mutable root.

**Mutable Root Invariant**: The source expression of a `let view` binding MUST be an active pinned mutable root (`let mut` handle or `mut` parameter). Creating a live view over an immutable `let` binding is statically rejected (`E0531`). Creating a live view over a reassignable `var` variable is statically rejected (`E0531`) to guarantee pointer stability. Conversely, immutable bindings safely share read-only access with other ordinary `let` bindings (`let b = a`).

```ebnf
LetViewDecl ::= "let" "view" Identifier [ ":" TypeExpression ] "=" Expression
```

```ril
type Node = { mut val: int }
let mut original = Node.{ val: 10 }

-- Live view aliases 'original' without write permissions:
let view observer = original
assert(observer.val == 10)

-- Writing through a view is statically prohibited:
-- observer.val = 20                   -- Error [E0520]: MutabilityLaunderingError: cannot mutate through read-only view 'observer'

-- Mutations to the underlying object are dynamically observed through the view:
original.val = 42
assert(observer.val == 42)             -- OK: live view reflects mutation

-- Target Constraint: source must be a pinned mutable root
let immutable_node = Node.{ val: 100 }
-- let view bad_view = immutable_node   -- Error [E0531]: ImmutableTargetViewError: cannot create live view over immutable binding 'immutable_node' (source must be pinned mutable root)

var reassignable_node = Node.{ val: 200 }
-- let view bad_var_view = reassignable_node -- Error [E0531]: ImmutableTargetViewError: cannot create live view over reassignable variable 'reassignable_node' (source must be pinned mutable root)

-- Safe read-only sharing via ordinary let:
let safe_alias = immutable_node        -- OK: immutable bindings safely share read-only access
assert(safe_alias.val == 100)

-- Concurrency Invariant:
-- A live mutable view cannot escape across a concurrent task boundary:
-- scope.fork(\-> observer.val)        -- Error [E0601]: CrossThreadDataRaceHazardError: cannot pass live mutable view across task boundary
```

### Type Declarations and Opaque Types

```ebnf
TypeDecl       ::= [ "pub" ] [ "halt" ] "type" Identifier [ GenericParams ] [ WhereClause ] "=" TypeExpression
OpaqueTypeDecl ::= [ "pub" ] "opaque" "type" Identifier [ GenericParams ] [ WhereClause ] "=" TypeExpression
```

```ril
-- Transparent Type Declarations:
pub type AccountId = int              -- Direct type alias, transparent across module boundaries
type Point = { x: int, y: int }        -- Local record type alias

-- Cyclic structural type alias rejection (E0313):
-- type BadCyclicA = { next: BadCyclicB }
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
EffectDecl   ::= [ "pub" ] "eff" Identifier [ GenericParams ] "{" EffectOpDecl { "," EffectOpDecl } [ "," ] "}"
               | [ "pub" ] "eff" Identifier [ GenericParams ] "{" TypeExpression { "," TypeExpression } [ "," ] "}"
EffectOpDecl ::= Identifier "(" [ ParameterList ] ")" [ "->" TypeExpression ] [ StateAnnot ]
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

```ril
-- In file: platform/dom.d.ril

-- Opaque nominal external types:
pub type DomWindow
pub type DomElement
pub type DomEvent

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
pub fn query_selector(win: DomWindow, sel: str) -> Result<DomElement, DomError>
pub fn set_attribute(mut elem: DomElement, key: str, val: str) -> () &mut
pub fn add_listener(elem: DomElement, event_type: str, handler: EventHandler) -> () @Async
where
    type EventHandler = fn(DomEvent) -> () &mut

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

---

## Expressions and Operators

### Operator Precedence and Associativity

| Level | Operators | Associativity | Description |
| :---: | :--- | :---: | :--- |
| **1** | `.` `?.` `?[` `[]` `()` `::` postfix `?` | Left | Member access (field or tuple index), safe navigation, indexing, invocation, postfix `?` |
| **2** | `-` `!` `~` `typeof` | Unary Prefix | Arithmetic negation, logical NOT, bitwise NOT, static type introspection |
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
```

### Pipeline Operators

- **Linear Pipeline (`|>`)**: Passes the left expression as the first argument to the right callable: `x |> f` desugars to `f(x)`.
- **Mutating Pipeline (`!>`)**: Passes the mutable left lvalue to the right mutating callable: `x !> f` desugars to `f(mut x)`.

```ril
let doubled = [1, 2, 3]
    |> Array::map(\x -> x * 2)
    |> Array::filter(\x -> x > 2)      -- Evaluates to [4, 6]

let mut items = [1, 2, 3]
items !> Array::push(4)                -- In-place mutation: items is now [1, 2, 3, 4]
```

### Error and Fallback Operators

- **Postfix `?`**: Unwraps `Ok(v)` / `Some(v)`, or returns early with `Err(e)` / `None` into the enclosing function frame.
   - **Enclosing Callable Requirement (`E0205`)**: Postfix `?` performs an early control transfer (return) into an enclosing activation frame. Evaluating postfix `?` outside an enclosing function or closure body (e.g., in module-scope declarations, initializers, or constant expressions) is statically rejected (`E0205: QuestionMarkOutsideFunctionError`), as no enclosing callable activation frame exists to receive propagated errors.
- **Fallback `??`**:
   - For `Option<T>`: Evaluates to `T` using the fallback value or supplier closure.
   - For `Result<T, E>`: Right operand MUST be an error-consuming closure `\err -> T`.
- **Safe Navigation `?.`, `?[`**: Evaluates to `None` if the target is `None`; otherwise accesses field or index safely.

```ril
fn find_record(id: int) -> Result<str, str> {
    let user = fetch_user(id)?         -- Early return Err if fetch_user fails
    Ok(user.name)
}
-- let bad_top_record = find_record(1)? -- Error [E0205]: QuestionMarkOutsideFunctionError: postfix '?' operator used outside function or closure body; no enclosing activation frame to receive early return

let opt: ?int = None
let v1 = opt ?? 100                    -- 100 (Option fallback with default value)
let v2 = opt ?? \-> compute_default()  -- Option fallback with lazy supplier closure

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

### Record Construction and Functional Update

```ril
type Point = { x: int, y: int, z: int }

let p1 = Point.{ x: 1, y: 2, z: 3 }
let p2 = Point.{ z: 10, ..p1 }         -- Functional record update: { x: 1, y: 2, z: 10 }
```

### Assignments and Compound Assignments

Assignments require an addressable mutable lvalue target. Assignments are expressions evaluating to `()`.

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
-- pinned_buf = Buffer.{ capacity: 64 } -- Error [E0502]: PinnedHandleReassignmentError: cannot reassign pinned mutable handle 'pinned_buf'; use 'var'

-- Chained assignment is prohibited:
-- x = y = 10                          -- Error [E0701]: ChainedAssignmentProhibitedError: assignment chaining is prohibited
```

---

## Control Flow and Pattern Matching

### Block Expressions, Tail Values, and Hoisted Declarations

A block `{ ... }` evaluates to its tail expression. A block may conclude with a trailing `where` clause (`BlockWhereClause`) declaring mutually recursive helper functions (`fn`), local types (`type`), and local algebraic effects (`eff`). All items in `BlockWhereClause` are hoisted across the enclosing block scope.

```ebnf
Block               ::= "{" [ StatementSequence ] [ TailExpression ] [ BlockWhereClause ] "}"
                      | "{" Expression "}"
StatementSequence   ::= Statement { Separator Statement } [ Separator ]
Statement           ::= LetDecl
                      | LetMutDecl
                      | VarDecl
                      | ScopedDecl
                      | LetViewDecl
                      | WithStatement
                      | ControlTransfer
                      | AssignmentExpr
                      | Expression
BlockWhereClause    ::= "where" BlockWhereItem { Separator BlockWhereItem } [ Separator ]
BlockWhereItem      ::= FunctionDecl | TypeDecl | EffectDecl
```

#### Block Expressions and Scope Invariants

- **Declarative Partitioning (`E0703`, `E0702`)**:
   - Declarations (`fn`, `type`, `eff`) MUST NOT appear in `StatementSequence` (`E0703`).
   - Variable bindings (`let`, `let mut`, `var`) MUST NOT appear in `where` clauses (`E0702`).
- **Local Effect Discharge (`E0618`)**:
   - Any local `eff` declared in `BlockWhereClause` MUST be completely discharged via an in-scope `with` handler within the enclosing block frame.
   - Local effects MUST NOT appear in outer `@Effect` annotations or escape into unhandled closures.
- **Local Nominal Confinement (`E0315`)**:
   - Local nominal wrappers (`type Id(T)`) and sum types (`type S { ... }`) MUST NOT appear in the return type of the enclosing function. Structural type aliases (`type Alias = T`) are exempt.

```ril
-- Mutually recursive functions and types hoisted in block 'where':
let total = {
    let base = compute_base()
    let parity = is_even(base)
    base
where
    fn compute_base() -> int { 100 }
    fn is_even(n: int) -> bool { if n == 0 { true } else { is_odd(n - 1) } }
    fn is_odd(n: int) -> bool { if n == 0 { false } else { is_even(n - 1) } }
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
-- fn bad_nominal_leak() -> Token {    -- Error [E0315]: EscapingLocalNominalTypeError: local nominal type 'Token' cannot escape declaring function
--     Token(42)
-- where
--     type Token(int)
-- }
```

### Conditional Expressions

`if` is an expression. Both branches must have compatible types. An `if` without an `else` evaluates to `()`.

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

### Control Transfers

Control transfers alter sequential evaluation order. Ril supports lexical control transfers (`last`, `next`, `return`) strictly scoped to the innermost enclosing loop or function. Ril deliberately omits loop labels to preserve syntactic clarity and guide multi-level escapes toward structured decomposition.

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
fn log_positive(val: int) {
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
OrPattern     ::= GuardPattern { "|" GuardPattern }
GuardPattern  ::= SinglePattern [ "if" Expression ]
SinglePattern      ::= LiteralPattern | VariablePattern | WildcardPattern
                     | TuplePattern | RecordPattern | ConstructorPattern | RangePattern
BindingModifier    ::= "mut" | "var"
VariablePattern    ::= [ BindingModifier ] Identifier
ConstructorPattern ::= QualifiedName [ "(" [ PatternList ] ")" ]
PatternList        ::= Pattern { "," Pattern } [ "," ]
TuplePattern       ::= "(" Pattern "," { Pattern "," } [ Pattern ] ")" | "(" ")"
RecordPattern      ::= [ TypeReference ] ".{" [ RecordPatternField { "," RecordPatternField } [ "," ] ] "}"
RecordPatternField ::= [ BindingModifier ] Identifier [ ":" Pattern ] | Identifier
```

Matches are evaluated top-to-bottom and must be exhaustive.

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
    Ok(p) -> println(p.1),               -- OK: whole-tuple binding (n = 1)
    Ok((code, msg)) -> println(msg),     -- OK: explicit tuple pattern unwrap
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
NarrowingFieldPath ::= Identifier "." Identifier [ "." Identifier ]
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
- **Non-Binding Predicates**: Pattern variables in `x is Variant(p)` are scoped strictly to trailing guards (`if guard`) and cannot escape to branch blocks (`E0301`).
- **Payload Projection ($S|_V$)**: Testing `x is V` refines sum type $S$ to variant $S|_V$ ([Sum Types and GADTs](#sum-types-and-gadts)):
   - $n = 0$: No payload; projection raises `E0301`.
   - $n = 1$: Projected via `.0` (`p.0`). `?T != None` directly unboxes to `T`.
   - $n \ge 2$: Projected via positional tuple indices `.0`, `.1`, ..., `.(n-1)`.
   - Record: Projected via declared field names (`x.field`).
- **Stability & Invalidation**:
   - `let`: Permanently narrowed across dominance region.
   - `var`: Reassignment (`=`, `+=`, `!>`) invalidates narrowing (`E0310`).
   - `let mut`: Tag identity is pinned (`E0502`); `mut` fields invalidate upon write.
- **Transitive Latent Havoc**: Invoking a callable transitively carrying mutable capability `&{mut v}` (via callee, arguments, or active effect handlers) resets $v$ to $T_{\text{root}}$.
- **Anti-Aliasing (`E0533`)**: Narrowing a `var` aliased by a live view (`let view`) or captured in a mutable closure (`&{mut x}`) is rejected (`E0533`). Copy to `let` to narrow.
- **Generic Confinement**:
   - Testing bare type parameters (`x is T`) is rejected (`E0301`).
   - GADT equations on $x$ are local to $x$ and do not rebind $T$ elsewhere in scope.
   - Mutable fields preserve container invariance ([Type Identity and Subtyping](#type-identity-and-subtyping)).
- **Dead Paths & Phase Ordering**:
   - Divergent branches (`never`) are pruned from joins ($\Gamma \sqcup \bot = \Gamma$).
   - Provably false predicates are rejected under `E0311`.
   - Dead-path pruning precedes Definite Mutation analysis (`E0527`); writes in dead paths do not count as reachable mutations.
- **Bounded Analysis**:
    - **Path Bound**: Field paths are tracked up to depth 3 (`a.b.c`); deeper paths default to $T_{\text{root}}$.
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
fn drain_cursor(var cursor: ?int) -> int {
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

-- Aliased narrowing hazard rejection (E0533):
fn test_aliased_hazard() {
    var raw: ?int = Some(10)
    let view v = raw                           -- Live view aliases 'raw'
    -- if raw != None {                        -- Error [E0533]: AliasedNarrowingHazardError: cannot narrow mutable variable 'raw' because it is aliased by live view 'v'; bind to immutable 'let' before branching
    --     println(raw + 1)
    -- }
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
        let mut step = \-> &{mut count} { count = None }
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
    -- if unused == None {
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
Parameter            ::= [ "mut" ] Identifier [ ":" TypeExpression ] [ "=" Expression ]

Argument             ::= [ Identifier ":" ] ( "mut" AssignTarget | Expression )
ArgumentList         ::= Argument { "," Argument } [ "," ]
CallExpr             ::= Expression "(" [ ArgumentList ] ")" [ TrailingClosure ]
TrailingClosure      ::= AnonFnExpr
```

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
- **Export Inlining**:
   - For `pub fn`, structural type aliases in `SignatureWhereClause` are canonically expanded in exported module interface artifacts (`.rilm`).

```ril
-- Signature-level where for complex higher-order pipeline:
pub fn process_stream<T, R, E>(
    stream: []T,
    transform: TransformFn<T, R, E>,
    sink: AuditSink<R>,
) -> Result<[]R, E> @Async &{mut audit_log}
where
    type TransformFn<In, Out, Err> = fn(In) -> Result<Out, Err> @Fiber + Async &mut
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

| Aspect | Named Function (`fn`) | Stateless Anonymous Function (`\x -> ...`) | Stateful Closure (`\x -> ... &closure`) |
| :--- | :--- | :--- | :--- |
| **Hoisting** | Module-wide newspaper ordering | Strictly lexical (definition before use) | Strictly lexical (definition before use) |
| **Environment Capture** | None (no captured state) | None (no captured state) | Lexically captured state (`&closure`) |
| **Type Representation** | Item identity / `fn(P) -> R` | `fn(P) -> R` | `fn(P) -> R &closure` |
| **Handle Requirement** | Direct call / `let` handle | Callable via `let` handle | `let` (read-only capture) or `let mut` / `var` (mut capture) |

### Parameter Modes, Caller Obligations, and Defaults

Ril enforces a strict distinction between shared read-only and borrowed mutable parameters:

```ril
type User = { mut name: str, mut score: int }

-- Borrowed mutable parameter: type MUST be reference type; function MUST declare &mut
fn add_score(mut u: User, points: int) &mut {
    u.score += points                  -- OK: in-place write to caller storage
}

let mut player = User.{ name: "Alice", score: 10 }

add_score(mut player, 5)               -- OK: explicit caller-site 'mut player'
player !> add_score(5)                 -- OK: mutating pipeline desugars to add_score(mut player, 5)

-- Static caller violations:
-- add_score(player, 5)                -- Error [E0520]: MutabilityLaunderingError: argument to 'mut' parameter must be passed with 'mut'
-- let frozen_player = player
-- add_score(mut frozen_player, 5)     -- Error [E0520]: MutabilityLaunderingError: cannot borrow read-only handle 'frozen_player' as 'mut'
-- fn bad_inc(mut count: int) &mut {}  -- Error [E0401]: ValueTypeMutableBorrowError: value types (int) cannot be declared as 'mut' parameters
-- fn noop_mut(mut u: User) &mut {}    -- Error [E0527]: UnusedMutableBindingError: 'mut' parameter 'u' declared but never modified
-- fn bad_rebind(mut u: User) &mut { u = User.{ name: "B", score: 0 } } -- Error [E0502]: PinnedHandleReassignmentError: cannot reassign pinned parameter 'u'
-- fn bad_var(var x: int) {}           -- Error [E0403]: VarParameterProhibitedError: 'var' parameters are prohibited in function signatures
```

#### Default Parameters and Named Arguments

- Default expressions MUST be pure expressions (zero unhandled effects, zero state mutations).
- Mutable parameters (`mut param: T`) CANNOT declare default values.
- Explicit arguments evaluate strictly left-to-right before omitted defaults.
- Named arguments allow order-independent binding at call sites.
- Generic parameters on function declarations (`fn name<...>`) CANNOT declare default types or values (`E0317`). All function generic parameters must be inferred from value arguments via bidirectional type checking or explicitly specified at call sites.

```ril
fn create_server(
    host: str,
    port: int = 8080,
    max_conn: int = 1000,
    enable_tls: bool = true,
) -> str {
    host ++ ":" ++ port ++ " (tls=" ++ enable_tls ++ ")"
}

-- Positional calls with defaults omitted:
let s1 = create_server("127.0.0.1")               -- host="127.0.0.1", port=8080, max_conn=1000, enable_tls=true
let s2 = create_server("0.0.0.0", 443)            -- host="0.0.0.0", port=443, max_conn=1000, enable_tls=true

-- Named argument calls:
let s3 = create_server("10.0.0.1", enable_tls: false) -- Order-independent named override
let s4 = create_server(host: "api.internal", port: 9000, enable_tls: true)

-- Rejections:
-- fn bad_def(mut u: User = User.{ name: "A", score: 0 }) {} -- Error [E0404]: MutableParameterDefaultProhibitedError: mutable parameter cannot have default
-- create_server("127.0.0.1", host: "duplicate")            -- Error [E0325]: DuplicateArgumentError: parameter 'host' supplied both positionally and by name
-- fn bad_fn_gen<T = int>(x: T) -> T { x }                  -- Error [E0317]: FunctionDefaultGenericProhibitedError: function generic parameter 'T' cannot declare default type; functions rely on caller-site bidirectional inference
```

### Anonymous Functions, Trailing Closures, and Projection Accessors

```ebnf
AnonFnExpr    ::= "\" [ AnonParams ] "->" ( Expression | Block )
AnonParams    ::= AnonParam { "," AnonParam } [ "," ]
AnonParam     ::= [ "mut" ] Identifier [ ":" TypeExpression ]
AccessorExpr  ::= "\" AccessorNav AccessorField { AccessorNav AccessorField }
AccessorNav   ::= "." | "?."
AccessorField ::= Identifier | TupleIndex
TupleIndex    ::= Digit { Digit }
```

- **Unary Desugaring Equivalence**: An `AccessorExpr` evaluates to a unary pure function projecting properties from its argument:
   - `\.field` desugars to `\x -> x.field`
   - `\.0` desugars to `\x -> x.0`
   - `\.field?.subfield` desugars to `\x -> x.field?.subfield`
   - `\?.field` desugars to `\x -> x?.field`
- **Product Type Duality**:
   - `Identifier` statically projects named fields from records (`{...}`), nominal wrappers, or refined named variants. Unmatched fields trigger static error `E0301`.
   - `TupleIndex` statically projects 0-indexed positional components from tuples (`(T0, T1, ...)`) or refined positional variant payloads ($S|_V$). Positional indices are statically checked at compile time against tuple arity $n$ ($0 \le i < n$). Out-of-bounds indices trigger `E0301`.
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

- **`&closure`**: Marks a callable value whose body captures variables from an enclosing scope.
- **`&capture`**: Marks a factory function that allocates and returns an escaping closure.
- Invoking closures that capture **read-only** variables requires only a standard `let` handle.
- Invoking closures that capture **mutable** variables strictly requires a `let mut` handle.

```ril
-- Factory returning a read-only capture closure:
fn make_adder(base: int) -> (fn(int) -> int &closure) &capture {
    \x -> base + x                     -- Captures immutable parameter 'base'
}

let add5 = make_adder(5)               -- Read-only handle 'let add5' suffices
let res1 = add5(10)                    -- 15: valid invocation through 'let' handle

-- Factory returning a mutable capture closure:
fn make_accumulator(start: int) -> (fn(int) -> int &closure) &capture {
    var total = start
    \step -> {
        total += step
        total
    }                                  -- Captures reassignable local 'total'
}

let mut acc = make_accumulator(100)    -- Requires 'let mut acc' (pinned mutable handle)
let a1 = acc(20)                       -- 120: valid invocation through 'let mut' handle

let frozen_acc = make_accumulator(10)
-- frozen_acc(5)                       -- Error [E0520]: MutabilityLaunderingError: cannot invoke mutable-capturing closure via read-only handle 'frozen_acc'

-- Nested Closures and Flat Chain Elaboration:
fn make_nested_multiplier(factor: int) -> (fn(int) -> (fn(int) -> int &closure) &closure) &capture {
    let base_multiplier = factor
    \multiplier_step -> {
        let intermediate = base_multiplier * multiplier_step
        \x -> x * intermediate         -- Elaborates flat capture set: &{closure make_nested_multiplier, base_multiplier, intermediate}
    }
}
```

### Higher-Order Functions and Capability Forwarding

Higher-order functions forward both algebraic effects and state capabilities transparently:

```ril
fn apply<T, R>(x: T, f: fn(T) -> R) -> R {
    f(x)                               -- Transparently forwards f's effects and state capabilities
}

-- Purity Conservation: Pure argument incurs ZERO obligations
let r_pure = apply(10, \x -> x * 2)   -- Pure call: zero effect, zero capability

-- Algebraic Effect Forwarding:
eff Logger { log(str) -> () }
fn logged_square(n: int) -> int @Logger {
    Logger::log("calculating")
    n * n
}
fn caller_with_effect() -> int @Logger {
    apply(5, logged_square)            -- Requires @Logger on caller_with_effect
}

-- State Capability Forwarding (&mut):
type Counter = { mut val: int }
let mut my_counter = Counter.{ val: 0 }
fn bump(mut c: Counter) &mut { c.val += 1 }

fn mutate_caller(mut c: Counter) &mut {
    apply(mut c, \mut target -> bump(mut target)) -- Transparently forwards &mut capability
}

-- External State Capability Forwarding (&{mut ident}):
var global_total = 0
fn add_to_global(n: int) -> int &{mut global_total} {
    global_total += n
    global_total
}

fn execute_global_step() -> int &{mut global_total} {
    apply(10, add_to_global)           -- Call site transparently inherits &{mut global_total}
}
```

---

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

-- Local Discharge of Retained Sharing (&^mut):
type NodeHub = { mut nodes: []int }
fn link(mut hub: NodeHub, node: int) &^mut { hub.nodes !> Array::push(node) }

fn test_internal_hub() -> int {
    let mut local_hub = NodeHub.{ nodes: [] }
    var local_node = 42
    link(mut local_hub, local_node)    -- &^mut discharged locally: all origins frame-confined
    len(local_hub.nodes)               -- Pure: signature carries NO &^mut!
}
```

### Parameter Mutation

A function mutating any borrowed parameter MUST declare `&mut`.

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

The boundary between frame-confined mutation and surviving retained aliasing is governed by **Surviving Write Path Counting**:

$$\mathcal{W}_{\text{surviving}}(\text{origin}) \ge 2 \iff \mathbin{\And}\hat{~}\mathrm{mut}$$

```
                ┌──────────────────────────────────────────────────┐
                │          SURVIVING WRITE PATH COUNTING           │
                └─────────────────────────┬────────────────────────┘
                                          │
                  ┌───────────────────────┴───────────────────────┐
                  ▼                                               ▼
         W_surviving = 1                                 W_surviving ≥ 2
   (Encapsulated Private Cell)                     (Retained Mutable Sharing)
   ───────────────────────────                     ──────────────────────────
   • Stack frame terminates                        • Multiple persistent paths
   • Only the closure holds the cell               • Stashed in external container
   • Requires &capture, &closure                   • Requires &^mut, &{^mut ident}
   • &^mut rejected as EXCESSIVE (E0529)           • Omitting triggers E0510
```

Retained mutable sharing occurs when execution creates a persistent writable access path that survives the call or closure publication boundary ($\ge 2$ independent surviving write paths). Origin identities survive intermediate local bindings: forwarding an external or borrowed reference through a local `let mut` handle does not alter its storage origin or discharge capability obligations. Conversely, allocating a fresh mutable reference that escapes solely through a single closure creates exactly 1 surviving write path and requires only `&capture`, while exposing multiple surviving handles creates $\ge 2$ write paths and requires `&^mut`.

```ril
type Hub = { mut entries: []Entry }
type Entry = { mut id: int }

-- Parameter Mutation ONLY (&mut):
-- Writable access to 'e' terminates at return; no persistent alias is created
fn touch_entry(mut e: Entry) &mut {
    e.id += 1
}

-- Anonymous Retained Mutable Sharing (&^mut):
-- Retains writable alias to parameter 'e' inside parameter 'h'; both survive the call
fn register_entry(mut h: Hub, mut e: Entry) &^mut {
    h.entries !> Array::push(e)        -- Survives call: 'e' is now aliased through 'h'
}

-- External Named Retained Mutable Sharing (&{^mut ident}):
-- Stashes a mutable parameter into an external global container
let mut global_hub = Hub.{ entries: [] }

fn publish_entry(mut e: Entry) &{^mut global_hub} {
    global_hub.entries !> Array::push(e) -- Survives call: 'e' is retained in global_hub
}

-- Returning a closure that captures and shares external mutable state:
var active_connections = 0

fn make_connection_ticker() -> (fn() -> int &{mut active_connections}) &{^mut active_connections} {
    \-> {
        active_connections += 1
        active_connections
    }
}

-- Intermediate Forwarding & Origin Tracking:
-- Forwarding an external or borrowed reference via a local 'let mut' handle retains '&^mut'
type Session = { mut count: int }
let mut global_session = Session.{ count: 0 }

fn make_forwarded_ticker() -> (fn() -> int &{mut global_session}) &{^mut global_session} {
    let mut forwarded = global_session -- Intermediate local handle
    \-> {
        forwarded.count += 1
        forwarded.count
    }                                  -- Tracks 'global_session' origin: MUST declare &{^mut global_session}
}
-- fn bad_forwarded_ticker() -> (fn() -> int &{mut global_session}) { ... }
-- Error [E0510]: MissingCapabilityAnnotationError: mutating external state requires caller signature to declare capability '&{^mut global_session}'

fn make_param_ticker(mut s: Session) -> (fn() -> int &closure) &^mut {
    let mut forwarded = s              -- Intermediate local handle
    \-> {
        forwarded.count += 1
        forwarded.count
    }                                  -- Survives call: caller and closure both retain write paths to 's'
}

-- Write Path Counting (Encapsulated Allocation vs. Retained Sharing):
-- Single surviving write path: encapsulated frame-confined allocation (requires &capture, NOT &^mut)
fn make_private_ticker() -> (fn() -> int &closure) &capture {
    let mut fresh_session = Session.{ count: 0 }
    let mut forwarded = fresh_session
    \-> {
        forwarded.count += 1
        forwarded.count
    }                                  -- OK: frame-confined origin; exactly 1 surviving write path
}
-- fn bad_over_annotated() -> (fn() -> int &closure) &^mut { ... }
-- Error [E0529]: ExcessiveCapabilityAnnotationError: excessive capability '&^mut', private allocation has no surviving aliases

-- Dual surviving write paths: both closure and reference escape (MUST declare &^mut)
fn make_dual_ticker() -> ((fn() -> int &closure), Session) &^mut {
    let mut fresh_session = Session.{ count: 0 }
    let runner = \-> { fresh_session.count += 1; fresh_session.count }
    (runner, fresh_session)            -- Both escape: caller receives 2 independent write paths to same origin
}

-- Covariant subsumption across capability lattice:
type Retainer = fn(mut Hub, mut Entry) &^mut
let f_retain: Retainer = register_entry -- Exact match
let f_touch: Retainer = \mut h, mut e -> { e.id += 1 } -- OK: &mut subsumed by &^mut
```

### External State Tracking

Accessing module-level or outer lexical bindings without passing them as parameters requires explicit named capability annotations:

```ril
let APP_CONFIG_NAME = "Production"
var transaction_count = 0

-- Read-only external access:
fn get_config_name() -> str &{APP_CONFIG_NAME} {
    APP_CONFIG_NAME                    -- OK: declared &{APP_CONFIG_NAME}
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

### Closure Capabilities and Handle Permissions

Invoking a closure that captured **mutable state** strictly requires the handle to be bound as `let mut`, `var`, or passed as a `mut` parameter. Calling through a read-only `let` handle triggers `Error [E0520]`. Invoking a closure with **read-only** captures requires only `let`.

```ril
-- Mutable-capturing closure:
fn create_counter(start: int) -> (fn() -> int &closure) &capture {
    var count = start
    \-> { count += 1; count }          -- Elaborates to: &{closure create_counter, mut count}
}

let mut active_counter = create_counter(0)
let v1 = active_counter()              -- OK: handle 'active_counter' is 'let mut'

let read_only_counter = create_counter(0)
-- read_only_counter()                 -- Error [E0520]: MutabilityLaunderingError: cannot invoke mutable-capturing closure via read-only handle 'read_only_counter'

-- Read-only capturing closure:
fn create_greeter(prefix: str) -> (fn(str) -> str &closure) &capture {
    \name -> prefix ++ ", " ++ name    -- Captures read-only 'prefix'
}

let greeter = create_greeter("Hello")  -- Bound as immutable 'let greeter'
let msg = greeter("Alice")             -- OK: read-only capture can be invoked via 'let' handle!
```

### Law of Exclusivity and Cross-Argument Disjointness

For every argument passed to a `mut` parameter, its memory path MUST be pairwise disjoint from every other argument and active closure capture in that call:

$$\forall i \in \mathrm{MutArgs},\quad \forall j \ne i,\quad \mathrm{Path}(a_i) \cap \mathrm{Path}(a_j) = \emptyset$$

```ril
type Node = { mut val: int }
type Pair = { mut first: Node, mut second: Node }
type Buffer = { mut size: int, mut data: []int }

fn swap_nodes(mut a: Node, mut b: Node) &mut {
    let tmp = a.val
    a.val = b.val
    b.val = tmp
}
fn append_buf(src: Buffer, mut dst: Buffer) &mut { ... }
fn modify_with(mut b: Buffer, cb: fn() -> ()) &mut {
    cb()
    b.size += 1
}

-- Record Field Disjointness:
let mut pair = Pair.{ first: Node.{ val: 1 }, second: Node.{ val: 2 } }
swap_nodes(mut pair.first, mut pair.second)   -- OK: pair.first ∩ pair.second = ∅ (provably distinct fields)
-- swap_nodes(mut pair.first, mut pair.first) -- Error [E0523]: MutMutAliasingConflictError: overlapping mutable borrow on 'pair.first'

-- Read-Mut Cross-Argument Conflicts:
let mut buf = Buffer.{ size: 0, data: [] }
-- append_buf(buf, mut buf)            -- Error [E0524]: ReadMutAliasingHazardError: 'buf' borrowed as mut while read-only borrowed

-- Array Element Disjointness:
let mut nodes = [Node.{ val: 10 }, Node.{ val: 20 }, Node.{ val: 30 }]
swap_nodes(mut nodes[0], mut nodes[1])        -- OK: distinct constant indices 0 and 1
let idx_a = 0; let idx_b = 0
-- swap_nodes(mut nodes[idx_a], mut nodes[idx_b]) -- Error [E0523]: MutMutAliasingConflictError: dynamic indices may overlap in multiple 'mut' arguments

-- Callback / Closure Aliasing Overlap:
let mut target = Buffer.{ size: 10, data: [1, 2] }

-- Callback captures read-only path overlapping mutable argument 'mut target':
-- modify_with(mut target, \-> { println(target.size) })
-- Error [E0524]: ReadMutAliasingHazardError: callback captures read-only path 'target' overlapping 'mut target'

-- Callback captures mutable path overlapping mutable argument 'mut target':
-- modify_with(mut target, \-> { target.size = 0 })
-- Error [E0523]: MutMutAliasingConflictError: callback captures mutable path 'target' overlapping 'mut target'
```

### Monotonic Permission Degradation and Anti-Laundering Matrix

Permissions degrade monotonically ($\text{Mut} \succ \text{ReadOnly} \succ \text{None}$). Converting a read-only handle into a mutable capability is statically rejected under the closed diagnostic matrix:

```ril
type UserDoc = { mut title: str, mut score: int }

-- E0520: MutabilityLaunderingError (binding/assigning read-only to let mut or mutable var, or mutating through view)
let doc = UserDoc.{ title: "Draft", score: 0 }
-- doc.score = 10                      -- Error [E0520]: MutabilityLaunderingError: cannot mutate field 'score' through read-only handle 'doc'
-- let mut laundered = doc             -- Error [E0520]: MutabilityLaunderingError: cannot bind read-only handle 'doc' to 'let mut'
let mut other_doc = UserDoc.{ title: "Active", score: 5 }
other_doc.score = 10                  -- OK: mutable handle mutated
-- other_doc = doc                    -- Error [E0502]: PinnedHandleReassignmentError: cannot reassign pinned mutable handle 'other_doc'; use 'var'
var reassignable_doc = UserDoc.{ title: "Active", score: 5 }
-- reassignable_doc = doc             -- Error [E0520]: MutabilityLaunderingError: cannot reassign read-only handle 'doc' to mutable handle 'reassignable_doc'
fn pass_to_mut(mut u: UserDoc) &mut { u.score += 1 }
-- pass_to_mut(mut doc)                -- Error [E0520]: MutabilityLaunderingError: cannot borrow read-only handle 'doc' as 'mut'

-- E0521: DestructureMutabilityLaunderingError (destructuring read-only into mut fields)
-- let .{ mut score } = doc            -- Error [E0521]: DestructureMutabilityLaunderingError: cannot bind read-only field 'score' to 'mut' pattern

-- E0522: ContainerMutabilityLaunderingError (injecting read-only reference into mutable container)
let mut doc_list: []UserDoc = []
-- doc_list !> Array::push(doc)        -- Error [E0522]: ContainerMutabilityLaunderingError: cannot store read-only reference 'doc' into mutable array 'doc_list'
let mut detached = doc |> clone        -- OK: clone() produces independent detached mutable duplicate
doc_list !> Array::push(detached)      -- OK: detached mutable root stored into mutable container

-- E0523 & E0524: Mut-Mut and Read-Mut aliasing hazards (see Law of Exclusivity)

-- E0525: SpreadLaunderingError (shallow-spreading read-only record into let mut root)
-- let mut spread_doc = UserDoc.{ ..doc, score: 99 } -- Error [E0525]: SpreadLaunderingError: shallow spread of read-only record 'doc' into 'let mut'

-- E0526: CollectionMutationDuringIterationError (mutating collection while iterating over it)
let mut nums = [1, 2, 3]
for nums as item {
    -- nums !> Array::push(item)       -- Error [E0526]: CollectionMutationDuringIterationError: cannot mutate collection 'nums' in place while iterating in 'for' loop
}

-- E0527: UnusedMutableBindingError (declared 'var', 'let mut', or 'mut' parameter but never modified)
-- var never_written = 42              -- Error [E0527]: UnusedMutableBindingError: variable 'never_written' declared 'var' but never modified or reassigned
-- let mut unused_doc = UserDoc.{ title: "X", score: 0 } -- Error [E0527]: UnusedMutableBindingError: variable 'unused_doc' declared 'let mut' but never modified in place
-- fn noop_mut(mut u: UserDoc) &mut {} -- Error [E0527]: UnusedMutableBindingError: 'mut' parameter 'u' declared but never modified

-- E0528: ReturnMutabilityLaunderingError (returning read-only parameter into caller let mut)
fn inspect_user(u: UserDoc) -> UserDoc { u }
let user_in = UserDoc.{ title: "Alice", score: 10 }
-- let mut stolen = inspect_user(user_in) -- Error [E0528]: ReturnMutabilityLaunderingError: cannot bind return value originating from read-only parameter 'user_in' to 'let mut'
let inspected = inspect_user(user_in)     -- OK: caller receives as read-only handle

-- E0529: ExcessiveCapabilityAnnotationError (over-annotating beyond minimal required capabilities)
-- fn pure_add(a: int, b: int) -> int &mut { a + b } -- Error [E0529]: ExcessiveCapabilityAnnotationError: function does not mutate parameters or state; remove unnecessary '&mut'

-- E0530: IllegalCapabilityCloneImmutError (target carries active capabilities: neither clonable nor freezable)
let mut counter_handle = create_counter(0)
-- let bad_clone = clone(counter_handle)       -- Error [E0530]: IllegalCapabilityCloneImmutError: cannot clone active capability or closure 'counter_handle'
-- let bad_immut = clone_immut(counter_handle) -- Error [E0530]: IllegalCapabilityCloneImmutError: target carrying active capabilities is neither clonable nor freezable into Immut<T>

-- E0531: ImmutableTargetViewError (creating a live view over an immutable binding)
let immutable_doc = UserDoc.{ title: "Frozen", score: 100 }
-- let view bad_v = immutable_doc       -- Error [E0531]: ImmutableTargetViewError: cannot create live view over immutable binding 'immutable_doc' (source must be mutable root)
let safe_alias = immutable_doc        -- OK: immutable binding safely shared across read-only handles
```

### Callable Signature Abstraction

Concrete captured variable names abstract behind `&closure`. Retained mutable sharing `&{^mut ident}` cannot be erased: it MUST abstract to both `&closure` and anonymous `&^mut`. Casting stateful callables to unannotated pure functions is strictly rejected.

```ril
var session_data = 0
let concrete_worker: fn(int) -> int &{mut session_data} = \delta -> {
    session_data += delta
    session_data
}

-- Valid Abstraction: Hiding variable name behind &closure
type Worker = fn(int) -> int &closure
let abstract_worker: Worker = concrete_worker -- OK: concrete &{mut session_data} satisfies &closure

-- Retained Sharing Abstraction: MUST retain &^mut
let mut hub = Hub.{ entries: [] }
let concrete_stashing: fn(Entry) -> () &{^mut hub} = \mut e -> {
    hub.entries !> Array::push(e)
}

type StashingWorker = fn(Entry) -> () &closure &^mut
let abstract_stashing: StashingWorker = concrete_stashing -- OK: preserves &^mut hazard

-- Illegal Hazard Erasure:
-- type BadWorker = fn(Entry) -> () &closure
-- let illegal: BadWorker = concrete_stashing -- Error [E0534]: HazardErasureProhibitedError: cannot erase '&^mut' hazard through abstraction
-- let pure_cast: fn(int) -> int = concrete_worker -- Error [E0534]: HazardErasureProhibitedError: cannot erase '&closure' to pure function
```

---

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
eff BufferIO {
    read_into(mut buf: []u8) -> int &mut, -- OK: Operation declares in-place buffer mutation
}

-- Effectful computation: invokes print twice and read_line once
fn hello() -> () @Console {
    Console::print("Enter name:")      -- First intercepted operation
    let name = Console::read_line()     -- Second intercepted operation
    Console::print("Hello, " ++ name)  -- Third intercepted operation (deep handler re-entered)
}

-- Effectful computation invoking capability-bearing BufferIO:
fn fill_header(mut target: []u8) -> int @BufferIO &mut {
    BufferIO::read_into(mut target)    -- OK: &mut capability flows through caller to operation
}
```

### Effect Handlers

`with` intercepts operations within its lexical scope, discharging the effect from the enclosing function's signature. When placed within a block, `with HandlerSpec` establishes the active deep handler for all subsequent expressions and statements in the remainder of that enclosing block. Handlers in Ril are **deep handlers**: evaluating `resume v` does not discard the handler; it remains active for all subsequent effect invocations until the block terminates.

Closures constructed in a scope with an active `with` handler **automatically capture the handler** into their heap environment (`&closure`), safely discharging the effect from the closure's public signature. Closures carrying unhandled effects that escape to heap records without an in-scope handler are statically rejected (`E0614`). Automatic handler capture (`&closure`) is strictly task-confined: handlers established in an enclosing scope MUST NOT be captured into closures crossing concurrent task boundaries (`scope.fork`, `Parallel::map`). Closures passed across concurrent task boundaries must be effect-confined ([Structured Concurrency and Panic Containment](#structured-concurrency-and-panic-containment)), rejected under `E0615` if unhandled effects or externally captured handlers are present.

```ebnf
WithExpr    ::= "with" HandlerSpec
HandlerSpec ::= "{" HandlerArm { "," HandlerArm } [ "," ] "}" | HandlerArm
HandlerArm  ::= QualifiedName "(" [ PatternList ] ")" "->" Expression
ResumeExpr  ::= "resume" Expression
```

```ril
-- Multi-Arm Statement Handler (like match block):
fn run_console() -> () {
    let mut log_entries: []str = []

    with {
        Console::print(msg) -> {
            log_entries !> Array::push(msg)
            resume ()                  -- Resumes computation; handler remains active
        },
        Console::read_line() -> resume "Alice",
    }

    hello()                            -- All 3 Console operations intercepted deeply
    -- @Console is fully discharged; run_console is purely functional externally
}

-- Single-Arm Statement Handler:
fn run_config() -> str {
    with Context::ask() -> resume "Production"
    Context::ask()                     -- Intercepted by single-arm handler
}

-- Automatic Handler Capture in Escaping Closures:
type Button = { label: str, on_click: fn() -> () }

fn make_button() -> Button {
    with Console::print(msg) -> resume ()

    -- Closure invokes Console::print. With 'with Console' active in scope,
    -- the active handler is captured into the closure environment:
    let cb = \-> Console::print("Button clicked!")
    -- 'cb' has type fn() -> () &closure (@Console discharged!)

    Button.{ label: "Save", on_click: cb } -- OK: safely stored in heap record!
}

-- Escaping Effect Closure Error (E0614):
-- fn bad_escape() -> Button {
--     let unhandled_cb = \-> Console::print("Dangling")
--     -- Error [E0614]: EscapingEffectClosureError: closure with unhandled effect '@Console' escapes to heap record without in-scope handler
--     Button.{ label: "Bad", on_click: unhandled_cb }
-- }
```

### Affine Resumption and Delimited Early Abort

`resume` is strictly one-shot (affine). Invoking `resume` more than once or escaping the handler arm is a compile-time static error. Returning from a handler arm without calling `resume` triggers delimited early abort, unwinding active `let scoped` resources in LIFO order. Physical memory mutations performed prior to the abort remain permanently committed (Commit-on-Write invariant; physical mutations are never rolled back).

```ril
-- Affine Resumption Violation: invoking resume more than once
fn bad_double_resume() -> int {
    with Op::query() -> {
        let first = resume 1
        -- let second = resume 2        -- Error [E0610]: DuplicateResumeInvocationError: affine resumption 'resume' invoked more than once
        first
    }
    Op::query()
}

-- Escaping Resumption Violation: resume escaping the handler arm
fn bad_escaping_resume() -> fn() -> int {
    with Op::query() -> {
        let esc = \-> resume 42         -- Error [E0611]: EscapingResumeError: affine resumption 'resume' cannot escape handler arm lexical scope
        esc
    }
    Op::query()
}

-- Delimited Early Abort with Proven LIFO Cleanup & Commit-on-Write Memory:
eff Auth {
    authenticate() -> bool,
}

type AuditLog = { mut entries: []str }

fn guarded_workflow(mut audit: AuditLog) -> str @Auth &mut {
    audit.entries !> Array::push("STEP_1")                               -- Physical mutation committed
    let scoped file = Resource.{ name: "vault.dat", on_close: \-> audit.entries !> Array::push("CLEANUP_FILE") }
    let scoped session = Resource.{ name: "admin_token", on_close: \-> audit.entries !> Array::push("CLEANUP_SESSION") }

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

Ril provides four foundational built-in algebraic effects tracking execution capabilities:

- **`@Fiber` (Cooperative Fiber Control)**: Low-level cooperative scheduling primitives (`yield`, `park`, `unpark`). Purely cooperative execution-quantum transfer without concurrent task branching authority.
- **`@Concurrent` (Structured Concurrency)**: High-level concurrent task forking, joining, racing, and timeout mechanics.
- **`@Async` (Suspendable I/O)**: An effect alias `{Fiber, Concurrent}` tracking uncolored asynchronous computations.
- **`@Div` (Divergence Tracking)**: Tracks potential non-termination in unbounded loops and general recursive functions. Total functions (`halt fn`) strictly prohibit `@Div`.

The sub-effect lattice satisfies:

$$\emptyset \subset \lbrace\text{Fiber}\rbrace \subset \lbrace\text{Fiber}, \text{Concurrent}\rbrace \equiv \text{Async}, \quad \text{disjoint from } \lbrace\text{Div}\rbrace$$

#### Normative Rules for Built-in System Effects
- **Least-Privilege Leaf I/O Principle (`@Fiber`)**: Leaf I/O operations requiring cooperative suspension without forking child tasks MUST declare only `@Fiber`. Holding `@Fiber` does not grant authority to fork concurrent tasks (`@Concurrent`), preserving frame containment and single-fiber DRF-SC invariants.
- **Compound Asynchronous Workflows (`@Async`)**: Functions that both suspend on I/O and manage concurrent child tasks declare `@Async`.
- **Decoupling Quantum Scheduling from Value Generators**: Cooperative scheduling operations declared within `eff Fiber` (`yield() -> ()` and `park() -> ()`) are strictly untyped quantum transfer primitives. Value-emitting streams MUST be modeled via user-defined algebraic effects (e.g., `eff Yield<T> { emit(T) -> () }`), evaluated as internal push streams under one-shot delimited resumption (`resume ()`). External pull iterators cannot escape `resume` past handler arm boundaries (`E0611`) and are constructed via state machines or fiber channels.

```ril
-- Built-in Fiber Effect Declaration:
eff Fiber {
    yield() -> (),                     -- Relinquishes quantum to runtime scheduler
    park() -> (),                      -- Suspends execution until external event/wakeup
    unpark() -> (),                    -- Awakens a parked fiber context
}

-- Leaf I/O Suspension Principle (@Fiber):
fn read_socket_chunk(fd: int) -> []u8 @Fiber {
    Fiber::park()                      -- Suspends execution until runtime I/O notification
    Socket::drain(fd)                  -- OK: leaf I/O without concurrent task forking authority
}

-- Functions declared @Fiber cannot invoke structured concurrency primitives:
fn bad_leaf_fork(fd: int) -> []u8 @Fiber {
    -- scope(\mut s -> {               -- Error [E0612]: UnhandledEffectError: function declares '@Fiber' but invokes unhandled '@Concurrent' primitive 'scope'
    --     s.fork(\-> Socket::drain(fd))
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
fn stream_remote_chunks(fd: int) -> () @Yield<[]u8> @Fiber {
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

All concurrent child tasks must be forked within a structured `scope`. A parent scope cannot exit until all child tasks finish. Panics and task failures in child tasks are isolated at the scope boundary and resolve to `Result<T, TaskFault>` (`TaskFault::Panicked`, `TaskFault::Cancelled`, or `TaskFault::DoubleFaultFatal`).

#### Normative Rules for Structured Concurrency
- **Lifetime Containment Invariant**:
   For any scope $S$ and any child task $c \in \text{Children}(S)$:
   $$\mathop{\mathrm{Lifetime}}(c) \subseteq \mathop{\mathrm{Lifetime}}(S) \subset \mathop{\mathrm{Lifetime}}(\text{Frame}_{\text{parent}})$$
- **Synchronous Scope Completion & Abort Barrier**:
   A `scope` block cannot complete or exit until all spawned child tasks reach a terminal state (`Completed`, `Panicked`, or `Cancelled`):
   - **Orderly Termination**: Normal scope completion blocks until all spawned tasks complete their execution.
   - **Synchronous Abort Barrier**: When an abnormal termination occurs (due to parent frame panic or child task defect), sibling tasks are immediately cancelled, and the scope boundary halts unwinding until all active children terminate and execute their `let scoped` LIFO cleanup handlers.
   - **Result Transfer**: Child return values $T$ are transferred upon `task.join()`, or discarded if the task is cancelled or unwound.
- **Boundary Capability Confinement**: Passing active mutable capabilities (`&mut`, `&^mut`, `&{mut var}`) or live views across concurrent task boundaries is statically rejected (`E0601: CrossThreadDataRaceHazardError`).
- **Concurrent Task Effect Confinement Invariant (`E0615`)**:
   For any concurrent child task $c$ spawned via `s.fork(task)` or data-parallel combinator (`Parallel::map`, `Parallel::fold`), the task callable $task$ MUST be closed under all user-defined algebraic effects:
   $$\mathop{\mathrm{Effects}}(task) \subseteq \lbrace\text{Fiber}\rbrace \quad \text{(or } \emptyset \text{ for pure/parallel combinators)}$$
   Every algebraic effect operation invoked within the execution tree of a concurrent child task MUST be intercepted and discharged by a local `with` handler lexically enclosed within that child task. Handlers established in parent or ancestor tasks MUST NOT be captured across concurrent task boundaries (`&closure`). Passing a callable carrying unhandled algebraic effects or capturing external effect handlers across a concurrent task boundary is statically rejected at compile time under `E0615: CrossTaskUnhandledEffectError`. Runtime-managed cooperative fiber scheduling operations (`eff Fiber`) are exempt.
```ril
use ril/concurrent::{scope, Scope, Task}

-- Core Structured Concurrency Fault Contracts:
pub type PanicInfo = {
    message: str,
    index: ?int,
}

pub type DoubleFaultInfo = {
    primary: PanicInfo,
    cleanup: PanicInfo,
}

pub type TaskFault {
    Panicked(PanicInfo),
    Cancelled,
    DoubleFaultFatal(DoubleFaultInfo),
}

-- Structured Concurrency and Task Panic Containment:
fn run_isolated_workers() -> Result<(str, int), TaskFault> {
    scope(\mut s -> {
        let task_ok = s.fork(\-> {
            "computation result"
        })

        let task_crash = s.fork(\-> {
            let scoped _buf = Resource.{ name: "worker_buf", on_close: \-> () }
            let divisor = 0
            100 / divisor              -- Child task panics: division by zero; _buf unwound in LIFO order
        })

        let ok_val = task_ok.join()?    -- Resolves to "computation result"

        -- Isolated panic containment: child panic does NOT crash the parent frame
        let err_val = match task_crash.join() {
            Ok(v) -> v,
            Err(TaskFault::Panicked(info)) -> {
                Logger::error("Child task panicked: " ++ info.message)
                0                       -- Gracefully handled in supervisor frame
            },
            Err(TaskFault::Cancelled) -> 0,
            Err(TaskFault::DoubleFaultFatal(df)) -> {
                Logger::fatal("Double fault: primary=" ++ df.primary.message ++ ", cleanup=" ++ df.cleanup.message)
                0
            },
        }

        Ok(ok_val, err_val)
    })
}

-- Concurrency Safety: Rejecting live mutable view across task boundary
fn bad_concurrent_data_race() {
    let mut shared_data = [1, 2, 3]
    scope(\mut s -> {
        -- s.fork(\-> {                -- Error [E0601]: CrossThreadDataRaceHazardError: cannot capture mutable handle 'shared_data' across concurrent task boundary
        --     shared_data !> Array::push(4)
        -- })
        Ok()
    })
}

-- Dynamic Task Fan-Out:
fn batch_transform(items: []int) -> Result<[]int, TaskFault> @Concurrent {
    -- Dynamic child tasks spawned in loops are bounded and tracked by the enclosing scope
    scope(\mut s -> {
        let mut tasks: []Task<int> = []
        for items as item {
            let t = s.fork(\-> item * 10)
            tasks !> Array::push(t)
        }

        let mut results: []int = []
        for tasks as t {
            results !> Array::push(t.join()?)
        }
        Ok(results)
    })
}

-- Concurrent Task Effect Confinement Invariant (E0615):
eff WorkerLog { log(str) -> () }

fn test_task_effect_confinement() {
    with WorkerLog::log(msg) -> resume ()      -- Active in parent activation frame

    scope(\mut s -> {
        -- Prohibited: child task carries unhandled effect; parent handler cannot cross task boundary:
        -- s.fork(\-> {
        --     WorkerLog::log("worker started") -- Error [E0615]: CrossTaskUnhandledEffectError: concurrent task closure carries unhandled effect '@WorkerLog'; external handlers cannot cross task boundary
        -- })

        -- Compliant: Effect is intercepted and discharged locally within the child task:
        let t = s.fork(\-> {
            with WorkerLog::log(msg) -> resume () -- Local handler confined to child fiber
            WorkerLog::log("worker started")      -- OK: discharged locally within child task
            42
        })
        let _ = t.join()
        Ok()
    })
}
```

### Deterministic Data Parallelism and Divide-and-Conquer Primitives

Data parallelism in Ril provides deterministic, multi-core evaluation of pure expressions over partitioned data structures and recursive divide-and-conquer workflows. Pure parallel evaluation carries **zero latent effects** ($\mathbf{Eff} = \emptyset$) in Domain III and is strictly distinguished from non-deterministic structured concurrency (`@Concurrent`).

#### The Colorless Parallel Principle and Domain Boundary
- **Zero-Effect Purity ($\mathbf{Eff} = \emptyset$)**:
   Data-parallel combinators (`Parallel::map`, `Parallel::fold`, `Parallel::join`, `Parallel::for_each`) are evaluation strategies of the abstract machine, not control inversion protocols. Functions orchestrating pure data parallelism remain completely colorless and may be called within total certified functions (`halt fn`). Attaching `@Parallel` annotations is an ontological category error and is statically rejected under `E0620: PseudoEffectAnnotationError`.
- **Observational Equivalence Axiom**:
   For any data-parallel evaluation $\mathbf{Parallel}::op(S, f)$, the observed terminal state (normal return value or defect panic) MUST be 100% bit-for-bit equivalent to sequential left-to-right evaluation on a single core.

#### Deterministic Reductions and Bit-Exact Floating-Point Trees
`Parallel::fold` evaluates associative reductions across slice partitions. Chunk-local accumulators utilize thread-local `&mut`, avoiding cross-core cache invalidation. Reductions merge intermediate results via a canonical binary tree ($G_{\text{canonical}} = 64$) guaranteeing bit-for-bit floating-point determinism across all architectures and core counts.

#### Observational Equivalence and Short-Circuit Determinism
For short-circuiting operations (`Parallel::find`, `Parallel::any`, `Parallel::first`), concurrent evaluation enforces the **Leftmost Index Supremacy Axiom**:

$$
\mathbf{Parallel}::find(S, P) \equiv \begin{cases}
  \text{Some}(S[k^{\ast}]) & \text{where } k^{\ast} = \min \lbrace i \in [0, |S|-1] \mid P(S[i]) = \text{true} \rbrace, \text{ if matches exist} \cr
  \text{None} & \text{if no match exists}
\end{cases}
$$

Under the **Deterministic Horizon & Cancellation Protocol**, when an arbitrary core finds a match at index $k$, it establishes a temporary upper bound (Horizon $H = k$). Partitions with lower indices $\gt k$ are immediately cancelled. Low-index partitions $\lt k$ MUST be completely evaluated; only if all low partitions yield no match is $k$ committed as the canonical result.

#### Canonical Leftmost Panic Precedence Rule
When multiple partitions trigger runtime Panics concurrently across different cores, the abstract machine enforces the **Canonical Leftmost Panic Precedence Rule**:

$$\pi_{\text{observed}} \equiv \pi_{\min(\mathcal{D})}, \quad \text{where } \mathcal{D} = \lbrace i \mid \text{evaluation of item } i \text{ triggers Panic} \rbrace$$

Panics at indices $j \gt \min(\mathcal{D})$ are treated as **Subsumed Defective Branches**. Furthermore:
- **Leftmost Panic Overrides Rightward Match**: A panic at index $k$ aborts and overrides a successful predicate match at index $j \gt k$.
- **Leftmost Match Suppresses Rightward Panic**: A successful short-circuit match at index $k$ suppresses and discards any potential panic at index $j \gt k$.

#### Lightweight Divide-and-Conquer (Parallel::join)
`Parallel::join` evaluates multiple pure thunks across available compute workers, joining execution synchronously at the parent call frame:
```ril
pub fn join<A, B>(task_a: fn() -> A, task_b: fn() -> B) -> (A, B)
pub fn join3<A, B, C>(task_a: fn() -> A, task_b: fn() -> B, task_c: fn() -> C) -> (A, B, C)
```
- **Stack Frame Borrowing Invariant**: The parent frame $\text{Frame}_ {\text{join}}$ synchronously blocks until all joined child tasks terminate. The contexts satisfy $\mathop{\mathrm{Lifetime}}(E_ {\text{child}}) \subseteq \mathop{\mathrm{Lifetime}}(\text{Frame}_ {\text{join}})$, allowing safe borrowing of parent stack data without heap allocation.
- **Linear Run-to-Completion**: Joined branches are effect-free ($\mathbf{Eff} = \emptyset$) and execute exactly once without cooperative quantum suspension or delimited re-entry.
- **Bernstein Disjoint Access Invariant (`E0619`)**: Parallel branches passed to `Parallel::join` MUST have mutually disjoint write and read sets:

   $$\mathrm{Write}(A) \cap (\mathrm{Read}(B) \cup \mathrm{Write}(B)) = \emptyset$$

   Simultaneous mutable access to overlapping memory paths across parallel branches triggers `E0619: ParallelDisjointAccessConflictError`. Concurrent branches in `Parallel::join` operate on distinct root variable bindings or pure expressions; low-level manual slice index splitting is disallowed in user code.
- **Transparent Panic Unwinding**: Joined panics unwind child frames in LIFO order and re-throw the primary panic into the parent frame without `TaskFault` reification. If both branches panic, the primary panic is selected via deterministic left-biased resolution.

#### Declarative Data Parallelism and Concurrency Bounding
- **`Parallel::for_each`**: Applies an in-place mutation closure `fn(mut T) -> () &mut` across slice elements (where element type `T` is a record or reference type with internal mutable fields). Element mutations execute in-place under abstract machine chunk scheduling. Closures are strictly forbidden from capturing external mutable variables (`E0605`).
- **`Parallel::map_bounded`**: Evaluates data-parallel transformations with bounded active parallel worker concurrency (`max_concurrency: int`). Observational equivalence and Leftmost Index Supremacy remain 100% bit-exact and identical to unconstrained evaluation.

#### The Absolute Effect-Free Parallel Invariant
In accordance with `E0615`, all callables passed to data-parallel combinators (`Parallel::map`, `Parallel::fold`, `Parallel::join`, `Parallel::for_each`) MUST be strictly closed with zero latent algebraic effects ($\mathbf{Eff} = \emptyset$). Environmental context, pseudo-random generator states, and configuration parameters MUST be passed explicitly as pure input values or deeply frozen `Immut<T>` graphs, preserving the single-stack affine resumption invariant without cross-thread continuation leakage.

```ril
use ril/parallel                      -- OK: automatically binds 'Parallel' namespace
use ril/concurrent::{scope, TaskFault}

-- Pure Data-Parallel Mapping (Colorless; callable in halt fn):
halt fn square_all(numbers: []f64) -> []f64 {
    numbers |> Parallel::map(\x -> x * x)
}

-- Floating-Point Deterministic Fold (G_canonical = 64):
let numbers: []f64 = [1.1, 2.2, 3.3, 4.4, 5.5, 6.6, 7.7, 8.8]
let total_sum = Parallel::fold(
    numbers,
    init_acc: \-> 0.0f64,
    fold_local: \acc, x -> acc + x,
    merge_acc: \a, b -> a + b
)

-- Observational Equivalence & Short-Circuit Leftmost Index Supremacy:
let data: []int = [10, 20, 30, 40, 50, 60, 70, 80]
let first_match = data |> Parallel::find(\x -> x > 25)
assert(first_match == Some(30))         -- Guaranteed Leftmost: 30, never 50 or 60

-- Canonical Leftmost Panic Precedence Rule:
let faulty_slice: []int = [10, 0, 50, 0, 100] -- index 1 and 3 are zero
let fault_result = scope(\mut s -> {
    let t = s.fork(\-> faulty_slice |> Parallel::map(\d -> 1000 / d))
    t.join()
})
match fault_result {
    Err(TaskFault::Panicked(info)) -> assert(info.index == Some(1)), -- Strictly index 1
    _ -> panic("expected deterministic panic at index 1"),
}

-- Lightweight Pure Divide-and-Conquer Fork-Join (Parallel::join):
pub fn parallel_merge_sort(s: []int) -> []int {
    if len(s) <= 1024 {
        return Array::sort(s)
    }
    let mid = len(s) / 2
    let left_slice = s[0..mid]
    let right_slice = s[mid..len(s)]

    let (sorted_l, sorted_r) = Parallel::join(
        \-> parallel_merge_sort(left_slice),
        \-> parallel_merge_sort(right_slice),
    )
    Array::merge(sorted_l, sorted_r)
}

-- In-Place Element Mutation (Parallel::for_each):
type Cell = { mut val: f64 }
let mut cells: []Cell = [Cell.{ val: 1.0 }, Cell.{ val: 2.0 }, Cell.{ val: 3.0 }, Cell.{ val: 4.0 }]
cells !> Parallel::for_each(\mut item -> { item.val *= 2.0 })
assert(cells[0].val == 2.0)

-- Concurrency-Bounded Execution (Parallel::map_bounded):
let urls: []str = ["api/a", "api/b", "api/c", "api/d"]
let hashes = urls |> Parallel::map_bounded(max_concurrency: 2, \u -> Crypto::sha256(u))

-- Negative Examples: Parallel Capability and Effect Confinement
var external_counter = 0
-- let bad_capture = data |> Parallel::map(\x -> {
--     external_counter += 1            -- Error [E0605]: InvalidParallelCapabilityError: cannot capture external mutable variable 'external_counter' in parallel combinator
--     x * 2
-- })

-- Parallel::join(
--     \-> { external_counter += 1 },   -- Error [E0619]: ParallelDisjointAccessConflictError: parallel branch captures mutable path 'external_counter' overlapping concurrent branch
--     \-> { external_counter += 2 },
-- )

-- fn bad_parallel_effect() -> () @Parallel {} -- Error [E0620]: PseudoEffectAnnotationError: '@Parallel' is an evaluation strategy of the abstract machine, not an algebraic effect
```

### Structured Concurrency Channels

Communication across concurrent tasks is mediated exclusively by structured message-passing channels (`ril/concurrent/channel`) and deeply frozen immutable values (`Immut<T>`). Ril strictly prohibits raw atomic shared memory primitives (`Atomic<T>`) and weak memory orderings.

#### Normative Rules for Structured Channels
- **Opaque Nominal Endpoint Types**: A channel is created as an asymmetric pair of Domain I opaque nominal endpoints:
   ```ril
   pub opaque type Sender<T>
   pub opaque type Receiver<T>
   ```
- **Endpoint Topology & Affine Uniqueness**:
   - Channels operate under MPSC (Multiple-Producer, Single-Consumer) topology.
   - `Sender<T>` implements explicit cloning (`clone(tx)`), allowing fan-out across worker tasks.
   - `Receiver<T>` is **affinely unique** and CANNOT be cloned (`E0530`). A channel has exactly one consumer.
- **Capability & Effect Signatures**:
   - Sending and receiving advance endpoint cursors in-place, requiring mutable capability (`&mut`) on the respective endpoint.
   - Suspendable channel operations declare cooperative suspension `@Fiber`.
- **Zero-Capability Payload Invariant (`E0602`)**:
   Values transmitted via `Sender::send` MUST carry zero active mutable capabilities and zero active views. Types permitted across channels are:
   - Scalar value types (`int`, `f64`, `bool`, `str`, `bytes`).
   - Immutable records, arrays, and tuples composed entirely of value types.
   - Deeply frozen immutable graphs (`Immut<U>`).
   - Detached channel endpoints (e.g., transmitting `Sender<U>`).
   Attempting to send types with interior mutable fields or active views triggers `E0602: IllegalChannelPayloadCapabilityError`.
- **Endpoint Aliasing Prohibition (`E0603`)**:
   Passing the same un-cloned `Sender<T>` handle to multiple concurrent tasks triggers `E0603: ChannelEndpointAliasingConflictError` (and `E0601`).

```ril
use ril/concurrent::{scope, TaskFault}
use ril/concurrent/channel              -- OK: automatically binds 'Channel' namespace
use ril/concurrent/channel::{Sender, Receiver}

type Message = { id: int, body: str }

fn run_channel_pipeline() -> Result<int, TaskFault> {
    scope(\mut s -> {
        let (tx, mut rx) = Channel::bounded<Message>(32)

        -- Producer 1: Cloned endpoint
        let mut tx1 = clone(tx)
        s.fork(\-> {
            tx1 !> Channel::send(Message.{ id: 1, body: "hello from worker 1" })?
            Ok()
        })

        -- Producer 2: Original endpoint
        let mut tx2 = tx
        s.fork(\-> {
            tx2 !> Channel::send(Message.{ id: 2, body: "hello from worker 2" })?
            Ok()
        })

        -- Consumer: Single unique receiver
        var count = 0
        while count < 2 {
            let msg = rx !> Channel::recv()?
            println(msg.body)
            count += 1
        }
        Ok(count)
    })
}

-- Negative Examples: Channel Boundary Safety
type MutableState = { mut count: int }
-- fn bad_channel_send(mut tx: Sender<MutableState>, s: MutableState) @Fiber &mut {
--     tx !> Channel::send(s)           -- Error [E0602]: IllegalChannelPayloadCapabilityError: payload type 'MutableState' contains mutable fields; cannot cross task boundary via Channel
-- }

-- fn bad_receiver_clone(rx: Receiver<int>) {
--     let rx_copy = clone(rx)          -- Error [E0530]: IllegalCapabilityCloneImmutError: 'Receiver<T>' is an affinely unique endpoint and cannot be cloned
-- }

-- fn bad_endpoint_aliasing(tx: Sender<int>) {
--     scope(\mut s -> {
--         s.fork(\-> { tx !> Channel::send(1) })
--         s.fork(\-> { tx !> Channel::send(2) }) -- Error [E0603]: ChannelEndpointAliasingConflictError: un-cloned sender endpoint 'tx' aliased across concurrent tasks
--     })
-- }
```

### Arrow-Only Law of Effects

Computations reduce to values in normal form. Once reduced, no further control transfers can occur. Passive values carry Shape and Access, but **zero latent effects**.

Attaching `@Eff` annotations to value bindings, record fields, tuple elements, or arrays represents an ontological category error and is statically rejected under `E0613: ValueEffectAnnotationError`:

```ril
-- -----------------------------------------------------------------------------
-- Negative Examples: Prohibited Value Effect Annotations (E0613)
-- -----------------------------------------------------------------------------
-- type BadField = { data: int @Io }            -- Error [E0613]: ValueEffectAnnotationError: record field 'data' has value type 'int'; raw effects cannot reside on values
-- type BadTuple = (str @Io, int)               -- Error [E0613]: ValueEffectAnnotationError: tuple component has value type 'str'; raw effects cannot reside on values
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

- **Expression Contexts**: In type functions and expression positions, ALL types without exception MUST be enclosed in `type<...>`:

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

- **Monopoly of Type Return Privilege Invariant**: Type declarations and pure type functions (`type`, `halt type`) strictly monopolize the authority to construct and return `type<T>`. Value-domain compile-time functions (`meta fn`) MUST NOT declare return sort `Type` or return `type<...>` (`E0812: MetaTypeReturnProhibitedError`). Types govern types; values govern values.
- **Read-Only Reflection Tokens in `meta fn`**: `meta fn` callables MAY accept `type<T>` as input parameters. Within `meta fn`, `type<T>` acts as an immutable, non-generative reflection token projecting properties of shapes into the value domain ($\mathcal{T} \to \mathcal{V}$, e.g. `byte_size(type<T>) -> int`). `meta fn` retains zero generative privilege to synthesize or mutate types.
- **Axiomatic Purity & Zero-Annotation Invariant**: Both type functions and `meta fn` evaluate strictly within the pure compile-time domain ($\mathbf{Eff} = \emptyset, \mathbf{Cap} = \emptyset$).
   - Type functions MUST NOT declare or carry algebraic effects (`@Effect`) or state capabilities (`&mut`, `&closure`, `&capture`, `&{ident}`) (`E0335`).
   - `meta fn` signatures MUST NOT declare algebraic effects or state capabilities (`E0813`).
   - Both enjoy full pure functional computation: local immutable bindings (`let`), conditionals (`if`), pattern matching (`match`), invocation of pure `meta fn` helpers, pure collection combinators, and recursion.
- **Totality Certification**: `halt type` certifies normal termination. Unmarked type functions operate under configurable evaluation step budgets (`E0811`). `halt fn` certifies total runtime execution.

```ril
-- Meta helper function: value domain computation only (returns int, not type<T>)
meta fn pad_align(size: int, align: int) -> int {
    (size + align - 1) & !(align - 1)
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
-- type BadInfinite<T> = BadInfinite<T>        -- Error [E0811]: CompileTimeBudgetExceededError: evaluation step budget exceeded in pure type function 'BadInfinite'
```

### Disjoint Call Families, Evaluation Budgets, and Branch Pruning

- **Family Isolation**: Type functions can invoke `meta fn` callables and other type functions, but cannot invoke runtime `fn` callables (`E0810`).
- **Runtime Isolation**: Runtime functions cannot invoke type functions (`E0810`).
- **Pre-Effect Dead-Branch Pruning Invariant**: In generic runtime functions with static meta guards (`if is_pure(type<F>)`), dead branches are pruned *prior to* latent effect row calculation ($\mathbf{Eff}$). An instance whose surviving branch is pure incurs zero latent effect obligations, preventing spurious effect pollution for callers.
- **Budget Exhaustion**: Exceeding evaluation step limits is statically rejected under `E0811`.

```ril
fn pure_worker(x: int) -> int { x + 1 }
fn effectful_worker(x: int) -> int @Console { Console::print("log"); x }

fn dispatch_worker<F>(f: F, val: int) -> int {
    meta let PURE = is_pure(type<F>)
    if PURE {
        f(val)                                 -- For pure_worker, surviving branch has Eff = ∅
    } else {
        f(val)                                 -- For effectful_worker, surviving branch carries @Console
    }
}

fn test_specialization() {
    let _ = dispatch_worker(pure_worker, 10)   -- OK: dead branch pruned, zero @Console required
}
```

### Unified Tripartite Introspection

Ril unifies compile-time introspection across all three composite data forms (Records, Sum Types, Tuples) under a single operator pair: `keyof T` and constituent projection `T.(K)`.

```ebnf
TypeProjection   ::= PrimaryType "." ( Identifier | TupleIndex | "(" Expression ")" )
TupleIndex       ::= Digit { Digit }
MappedRecordType ::= "{" "[" Identifier "in" Expression "]" ":" TypeExpression "}"
MappedTupleType  ::= "(" "[" Identifier "in" Expression "]" ":" TypeExpression ")"
```

#### Universal Coordinate Indexing
In expression and meta contexts, `keyof T` queries the coordinate index set of composite type $T$:
- **Records**: Evaluates to an immutable array `[]str` of field names sorted strictly in UTF-8 byte order.
- **Sum Types (ADTs)**: Evaluates to an immutable array `[]str` of variant constructor names sorted strictly in UTF-8 byte order.
- **Tuples**: Evaluates to an immutable array `[]int` of positional indices `[0, 1, ..., n-1]` in monotonic ascending order.
- **Leibniz Invariance**: Canonical sorting guarantees that structurally equivalent types produce identical coordinate index arrays ($T_1 \equiv T_2 \implies \text{keyof } T_1 \equiv \text{keyof } T_2$).

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
- **Mapped Records (`{ [K in Expr]: TypeExpr }`)**: `Expr` MUST evaluate to compile-time `[]str`. Supplying `[]int` triggers `E0341: InvalidRecordKeySortError`. Both Records and Sum Types can be mapped symmetrically:
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

type Pick = \T, Included: []str -> {
    let valid_keys = keyof T |> Array::filter(\k -> Included |> Array::contains(k))
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
TypeMatchExpr    ::= "match" "type" "<" TypeExpression ">" "{" { TypeMatchArm } "}"
TypeMatchArm     ::= TypePattern [ "if" Expression ] "->" Expression
TypePattern      ::= "type" "<" TypePatternInner ">" | "_"
TypePatternInner ::= RigidNominalPattern | TuplePattern | RecordPattern
                   | ArrayPattern | MapPattern | PrimitivePattern | Wildcard | "let" PascalCase
```

- **Scoped Pattern Variables (`let U`)**: A `let U` binder inside `type<P>` introduces an immutable type variable scoped strictly to the arm's guard and RHS expression. `U` MUST be `PascalCase` (`E0101`).
- **Linearity Invariant**: Pattern variables MUST be linear; repeating the same identifier within a pattern branch is statically rejected (`E0203: DuplicateDeclarationError`). Multi-position equality is asserted via explicit guards (`if type<A> == type<B>`).
- **Rigid Head Invariant**: The outermost constructor of a type pattern must be a rigid, known nominal constructor (e.g. `Option<let U>`). Binding the type constructor itself as a variable pattern (`(let M)<let U>`) is statically rejected (`E0306: KindMismatchError`).

```ril
-- Deep Recursive Unwrapping of Container / Fallible Types:
halt type UnwrapAll = \T -> match type<T> {
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
type Elem = ElementOf<[]str>                   -- str
type HeadTail = DeconstructTuple<(u8, i32, f64)>-- { head: u8, tail: (i32, f64) }

-- Rejection of Non-Rigid Type Patterns (E0306):
-- type BadPattern = \T -> match type<T> {
--     type<(let M)<let U>> -> type<U>,         -- Error [E0306]: KindMismatchError: rigid type pattern cannot bind constructor '(let M)' as a higher-kinded pattern variable
--     _                    -> type<never>,
-- }
```

### Static Parameter Sorts and Adaptation Rules

Type functions accept four parameter sorts:

- **Bare Types (`\T` or `\T: Type`)**: Accepts static type expressions. Unannotated parameters default to sort `Type`.
- **Const Values (`\param: ValueType`)**: Accepts compile-time known constants (literals, `meta let`, statically foldable expressions). Passing runtime variables raises `E0810`.
- **Bounded & Structural Types (`\T: { id: int, ..R }`, `\K: keyof T`)**: Enforces structural row subtyping and coordinate key inclusion.
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

`meta let` and `meta fn` execute strictly during compilation under deterministic totality budgets. Values produced by `meta` evaluation degrade monotonically into immutable constants and inlined immediates ($\text{Meta} \succ \text{Runtime}$).

**Cooperation Pattern**: `meta fn` computes hardware alignments, pad bytes, and metrics; type functions ingest those values to synthesize specialized data structures.

```ril
-- Pure compile-time layout calculations (meta fn: returns values only):
meta fn align_to(offset: int, alignment: int) -> int {
    (offset + alignment - 1) & !(alignment - 1)
}

meta fn compute_padding(offset: int, alignment: int) -> int {
    align_to(offset, alignment) - offset
}

-- Parametric inspection: strictly no 'any'
meta fn primitive_size<T>(_t: type<T>) -> int {
    match type<T> {
        type<u8> | type<i8> | type<bool>   -> 1,
        type<u16> | type<i16>              -> 2,
        type<u32> | type<i32> | type<f32>  -> 4,
        type<u64> | type<i64> | type<f64>  -> 8,
        type<[]_>                          -> 16, -- Managed slice header
        _                                  -> 8,  -- Managed object reference
    }
}

-- Specialized packet layout generator:
halt type AlignedPacket = \HeaderType, PayloadType, align_boundary: int = 8 -> {
    meta let HEADER_BYTES = primitive_size(type<HeaderType>)
    meta let PAD_BYTES = compute_padding(HEADER_BYTES, align_boundary)
    
    if PAD_BYTES == 0 {
        type<{
            header: HeaderType,
            payload: PayloadType,
        }>
    } else {
        type<{
            header: HeaderType,
            _pad: [PAD_BYTES]u8,
            payload: PayloadType,
        }>
    }
}

-- Storage hierarchy specialization:
halt type OptimizedStorage = \capacity_bytes: int -> {
    meta let ALIGNED_CAP = align_to(capacity_bytes, 16)
    if ALIGNED_CAP <= 128 {
        type<{
            inline_buf: [ALIGNED_CAP]u8,
            len: int,
        }>
    } else {
        type<{
            heap_ptr: int,
            capacity: int,
            len: int,
        }>
    }
}

type FastPacket = AlignedPacket<u32, u64, 8>   -- { _pad: [4]u8, header: u32, payload: u64 }
type SmallBuffer = OptimizedStorage<60>         -- { inline_buf: [64]u8, len: int }
type LargeBuffer = OptimizedStorage<1024>       -- { capacity: int, heap_ptr: int, len: int }

-- Static assertions:
meta let _ = assert(align_to(4, 8) == 8, "alignment calculation verified")
-- meta let _ = assert(align_to(4, 8) == 16, "fails") -- Error [E0830]: MetaAssertionFailedError: compile-time assertion 'align_to(4, 8) == 16' evaluated to false: fails
```

---

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

pub fn circle_area(radius: f64) -> f64 {
    PI * radius * radius                -- OK: internal access to private 'PI'
}

-- In file: platform/fs.d.ril (External Interface Declaration Unit)
pub type FileHandle                     -- OK: opaque nominal external type
pub fn read_file(path: str) -> Result<[]u8, str> @Async -- OK: bodyless external signature

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

Top-level declarations MUST be free of observable runtime side effects. Top-level mutable variables must be initialized with constant expressions. Furthermore, evaluating postfix `?` outside a function or closure body (such as in top-level declarations or module-scope expressions) is strictly prohibited (`E0205: QuestionMarkOutsideFunctionError`) because there is no enclosing callable activation frame to receive propagated fallible outcomes.

```ril
let MAX_CONNECTIONS: int = 100
let DEFAULT_TITLE: str = "Ril Application"
var active_workers: int = 0            -- OK: initialized with constant expression

-- Prohibited top-level runtime side effects and error propagation:
-- let current_time = Clock::now()      -- Error [E0202]: TopLevelSideEffectError: top-level declaration must be a pure constant expression
-- let db = Database::connect("db.loc") -- Error [E0202]: TopLevelSideEffectError: top-level declaration cannot invoke runtime I/O or effects
-- let top_parse = parse_id("10")?      -- Error [E0205]: QuestionMarkOutsideFunctionError: postfix '?' operator used outside function or closure body; no enclosing activation frame to receive early return
```

### Test Conventions and Execution Protocol

Test entry points are ordinary public functions conforming to the naming prefix `test_*` and returning either `()` or `Result<(), E>`. Test functions evaluate within isolated activation frames and enforce domain invariants via standard assertions:

- **Pure & Direct Tests**: Functions returning `()` verify invariants using deterministic runtime panics on breach (`assert`).
- **Fallible Tests**: Functions returning `Result<(), E>` enable cascading error propagation via postfix `?`. Returning `Err(e)` indicates test assertion failure.
- **Hermetic Scoped Mocking**: Environmental algebraic effects are mocked within standard lexical blocks `{ with HandlerSpec; logic }`. The handler is automatically popped upon exiting the block. Unhandled operations trigger deterministic panics or domain errors under the Hermetic Sandbox invariant.
- **Panic Isolation Assertion**: Asserting that defective operations trigger deterministic runtime panics is evaluated across structured concurrency task boundaries (`scope.fork`), capturing faults into `TaskFault::Panicked` without violating synchronous frame panic isolation.
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
                panic("Unexpected mock query: " ++ sql)
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
        let scoped res = Resource.{
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

pub fn test_out_of_bounds_defect() -> Result<(), str> {
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

Executable programs define a root `main` function:

```ril
pub fn main() -> () {
    println("Hello, Ril!")
}

-- Fallible main:
pub fn main() -> Result<(), str> {
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
| `[K: V]` | Type | Built-in associative map |
| `Array` | Module | Standard dynamic array combinators and mutation primitives (`push`, `pop`, `map`, `filter`, `fold`, `contains`, `reverse`) |
| `Map` | Module | Standard associative map combinators and access primitives (`get`, `set`, `remove`, `contains`, `keys`, `values`) |
| `Set` | Module | Standard unique set operations and algebraic combinators (`contains`, `insert`, `remove`, `union`, `intersect`, `diff`) |
| `String` | Module | Standard string operations and character inspection (`split`, `trim`, `contains`, `replace`, `starts_with`, `ends_with`) |
| `inner(wrapper)` | Function | Extracts underlying value from nominal wrapper `type W(T)` |
| `clone(x)` | Function | Allocates deep independent mutable duplicate of heap reference |
| `clone_immut(x)` | Function | Freezes heap object into permanently immutable `Immut<T>` |
| `derive(base, recipe)` | Function | Path-wise copy-on-write functional update over reference graph |
| `len(coll)` | Function | Returns element count of string, bytes, array, map, or set |
| `panic(msg)` | Function | Initiates deterministic runtime panic unwinding |
| `assert(cond, msg)` | Function | Verifies invariant; panics on breach |
| `print(s)`, `println(s)` | Functions | Writes text to standard output |

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
let mut original = [1, 2, 3]
let mut detached = clone(original)
detached !> Array::push(4)             -- Mutates 'detached'; 'original' remains [1, 2, 3]

-- Permanent Immutability Freezing via clone_immut():
let frozen: Immut<[]int> = clone_immut(original)
-- frozen !> Array::push(5)            -- Error [E0520]: MutabilityLaunderingError: cannot mutate permanently immutable Immut<T>

-- Functional Derivation via derive():
let base_cfg = .{ theme: "dark", retries: 3 }
let updated_cfg = base_cfg |> derive \mut next -> {
    next.theme = "light"
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

Under the **Anti-Fault Masking Invariant**, any expression evaluating to `Result<T, E>` MUST be explicitly inspected, propagated, matched, or unpacked. Discarding a fallible `Result` without inspection is statically rejected (`E0720`).

```ril
fn save_profile(user_id: int) -> Result<(), str> {
    if user_id <= 0 { Err("invalid id") } else { Ok() }
}

fn process_request(id: int) -> Result<(), str> {
    -- Prohibited: discarding fallible Result without inspection
    -- save_profile(id)                 -- Error [E0720]: UnusedFallibleResultError: unused fallible Result must be handled

    -- Compliant Alternative 1: Postfix '?' error propagation
    save_profile(id)?

    -- Compliant Alternative 2: Explicit pattern matching
    match save_profile(id) {
        Ok() -> Logger::info("Profile saved"),
        Err(e) -> Logger::error("Save failed: " ++ e),
    }

    -- Compliant Alternative 3: Fallback error closure
    save_profile(id) ?? \err -> Logger::warn("Handled fallback: " ++ err)

    Ok()
}
```

---

## Diagnostic Error Codes Summary

| Code | Diagnostic Name | Normative Condition |
| :---: | :--- | :--- |
| **`E0101`** | `InvalidIdentifierCasingError` | Identifier casing style violates grammatical role requirement |
| **`E0102`** | `MalformedIdentifierSyntaxError` | Identifier contains illegal consecutive/trailing underscores or unnormalized acronym casing |
| **`E0103`** | `PatternCasingCollisionError` | Pattern binding position contains illegal casing causing semantic collision |
| **`E0201`** | `PrivateItemAccessError` | Accessing or importing unexported private module symbol |
| **`E0202`** | `TopLevelSideEffectError` | Top-level declaration contains non-constant runtime side effects |
| **`E0203`** | `DuplicateDeclarationError` | Redeclaring an existing identifier in the same scope |
| **`E0204`** | `UnresolvedIdentifierError` | Reference to an undeclared or unimported identifier in lexical scope |
| **`E0205`** | `QuestionMarkOutsideFunctionError` | Using postfix '?' operator outside an enclosing function or closure body (no enclosing activation frame to receive early return) |
| **`E0301`** | `TypeMismatchError` | Expression type incompatible with expected type |
| **`E0302`** | `UnexpectedFieldError` | Closed record supplied with undeclared fields |
| **`E0303`** | `NonExhaustiveMatchError` | Pattern match expression does not cover all possible variant or structural cases |
| **`E0304`** | `UnreachableMatchArmError` | Pattern match arm is statically unreachable due to preceding exhaustive patterns or GADT index constraints |
| **`E0305`** | `NominalTypeMismatchError` | Mismatched nominal type wrapper identities |
| **`E0306`** | `KindMismatchError` | Mismatched higher-kinded type constructor or sort constraint |
| **`E0307`** | `MissingFieldError` | Record projection or construction expression lacks required declared field |
| **`E0308`** | `OpaqueBoundaryViolationError` | Attempting to unpack, penetrate with `inner()`, or pattern deconstruct an opaque type externally |
| **`E0309`** | `VacuousBindingError` | 'let' pattern binds zero variables (excluding explicit wildcard discard 'let _ = expr') |
| **`E0310`** | `InvalidatedNarrowingAccessError` | Accessing identifier whose flow narrowing was invalidated by reassignment or mutation |
| **`E0311`** | `ContradictoryNarrowingError` | Narrowing predicate is statically unsatisfiable under active flow environment |
| **`E0312`** | `TupleIndexOutOfBoundsError` | Static tuple index projection exceeds bounds of tuple type |
| **`E0313`** | `CyclicTypeAliasError` | Structural type aliases form a cyclic dependency without nominal or sum indirection |
| **`E0314`** | `ArityMismatchError` | Mismatched number of arguments supplied to constructor, nominal wrapper, or tuple pattern |
| **`E0315`** | `EscapingLocalNominalTypeError` | Local nominal wrapper or sum type escapes enclosing function boundary as return type |
| **`E0316`** | `NonTrailingDefaultGenericParamError` | Generic parameter without default follows generic parameter with default |
| **`E0317`** | `FunctionDefaultGenericProhibitedError` | Function generic parameter declares default type or value argument |
| **`E0318`** | `LiteralTypeProhibitedError` | Value literal used directly as a type expression without singleton wrapper |
| **`E0319`** | `BareTypeInExpressionContextError` | Bare type name used in expression context without enclosing `type<...>` wrapper |
| **`E0320`** | `ForwardTypeDefaultReferenceError` | Generic default parameter expression contains forward reference or circular dependency |
| **`E0321`** | `NonDivergentElseError` | 'let ... else' block does not diverge via control transfer ('return', 'panic', 'last') |
| **`E0322`** | `WildcardExpressionError` | Standalone wildcard '_' used in expression position outside pattern binding or discard context |
| **`E0323`** | `ConstGenericSortMismatchError` | Const generic argument does not match expected parameter sort |
| **`E0324`** | `DynamicRecordIndexProhibitedError` | Dynamic expression indexing attempted on closed static record type |
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
| **`E0401`** | `ValueTypeMutableBorrowError` | Attempt to declare or pass a value type as `mut` parameter |
| **`E0402`** | `ValueTypePinnedMutError` | Attempting to declare a value type as pinned mutable handle `let mut` |
| **`E0403`** | `VarParameterProhibitedError` | Attempting to declare a function parameter with `var` |
| **`E0404`** | `MutableParameterDefaultProhibitedError` | Function parameter declared 'mut' specifies a default value argument |
| **`E0501`** | `ImmutableReassignmentError` | Reassigning an immutable `let` binding |
| **`E0502`** | `PinnedHandleReassignmentError` | Reassigning a pinned mutable handle `let mut` or borrowed `mut` parameter |
| **`E0510`** | `MissingCapabilityAnnotationError` | Calling mutating operation without declaring `&mut` or `&^mut` |
| **`E0520`** | `MutabilityLaunderingError` | Binding or assigning read-only handle to `let mut` or mutable `var`, or mutating through view |
| **`E0521`** | `DestructureMutabilityLaunderingError` | Destructuring read-only reference record into `mut` or `var` pattern fields |
| **`E0522`** | `ContainerMutabilityLaunderingError` | Injecting read-only reference into mutable collection |
| **`E0523`** | `MutMutAliasingConflictError` | Overlapping mutable arguments passed to `mut` parameters |
| **`E0524`** | `ReadMutAliasingHazardError` | Mutable argument aliases simultaneous read-only argument |
| **`E0525`** | `SpreadLaunderingError` | Shallow-spreading read-only record into `let mut` or `var` root |
| **`E0526`** | `CollectionMutationDuringIterationError` | Mutating collection in place while iterating in `for` loop |
| **`E0527`** | `UnusedMutableBindingError` | `var`, `let mut`, or `mut` parameter never modified or reassigned along any path |
| **`E0528`** | `ReturnMutabilityLaunderingError` | Returning read-only parameter into caller `let mut` or `var` handle |
| **`E0529`** | `ExcessiveCapabilityAnnotationError` | Over-annotating signature beyond minimal required capabilities |
| **`E0530`** | `IllegalCapabilityCloneImmutError` | Target carrying active capabilities or scoped handles is neither clonable nor freezable into `Immut<T>` |
| **`E0531`** | `ImmutableTargetViewError` | Attempting to create a live view (`let view`) over an immutable binding or non-pinned handle |
| **`E0532`** | `ReassignableScopedResourceError` | Attempting to declare a scoped resource binding with `var scoped` |
| **`E0533`** | `AliasedNarrowingHazardError` | Narrowing a `var` binding aliased by a live view or captured in a mutable closure |
| **`E0534`** | `HazardErasureProhibitedError` | Callable abstraction attempting to erase '&^mut' hazard or convert stateful closure to pure function |
| **`E0601`** | `CrossThreadDataRaceHazardError` | Passing live mutable view across concurrent task boundary |
| **`E0602`** | `IllegalChannelPayloadCapabilityError` | Transmitting payload carrying active mutable capabilities, views, or unfrozen references across channel |
| **`E0603`** | `ChannelEndpointAliasingConflictError` | Borrowing same un-cloned channel endpoint across concurrent tasks |
| **`E0605`** | `InvalidParallelCapabilityError` | Capturing external mutable capabilities in parallel combinator |
| **`E0607`** | `DerivedProxyEscapeError` | Derived proxy escapes 'derive' recipe via return, assignment, or closure publication |
| **`E0610`** | `DuplicateResumeInvocationError` | Invoking affine one-shot resumption `resume` more than once |
| **`E0611`** | `EscapingResumeError` | Escaping resumption handle beyond handler arm lexical scope |
| **`E0612`** | `UnhandledEffectError` | Invoking effect operation without in-scope handler or declaring effect in callable signature |
| **`E0613`** | `ValueEffectAnnotationError` | Attaching algebraic effect annotation ('@Eff') to a non-callable type expression or value binding |
| **`E0614`** | `EscapingEffectClosureError` | Closure with unhandled effect escaping to heap record without in-scope handler |
| **`E0615`** | `CrossTaskUnhandledEffectError` | Passing callable with unhandled effect or external effect handler across concurrent task boundary |
| **`E0616`** | `ScopedCleanupEffectError` | Resource cleanup handler (`on_close`) declares or invokes unhandled algebraic effects |
| **`E0617`** | `ScopedCleanupDivergenceError` | Resource cleanup handler (`on_close`) declares or invokes divergent operations (`@Div`) |
| **`E0618`** | `UndischargedLocalEffectError` | Local algebraic effect declared in 'where' is not completely discharged within enclosing block |
| **`E0619`** | `ParallelDisjointAccessConflictError` | Parallel branches in `Parallel::join` capture or access overlapping mutable memory paths (Bernstein violation) |
| **`E0620`** | `PseudoEffectAnnotationError` | Attaching non-effect evaluation strategy (such as '@Parallel') as an algebraic effect annotation |
| **`E0701`** | `ChainedAssignmentProhibitedError` | Chaining assignments (`a = b = c`) |
| **`E0702`** | `InvalidWhereItemError` | Declaring variable binding or non-hoistable item in `where` clause |
| **`E0703`** | `IllegalSequentialDeclarationError` | Declaring 'fn', 'type', or 'eff' in sequential statement stream instead of 'where' clause |
| **`E0704`** | `InvalidSignatureWhereItemError` | Declaring 'fn' or 'eff' in signature 'where' clause (signature where is restricted to 'type') |
| **`E0705`** | `DownwardScopeReferenceError` | Signature 'where' clause references item declared in inner block 'where' clause |
| **`E0706`** | `SignatureTypeNotInWaistWhereError` | Function signature references type declared in block 'where' clause instead of signature 'where' clause |
| **`E0707`** | `InvalidControlTransferContextError` | Using 'last' outside loop or 'return' across prohibited boundary |
| **`E0710`** | `IllegalControlTransferInFallbackError` | Embedding `return`/`last` in fallback operator `??` |
| **`E0711`** | `InvalidResultFallbackError` | Supplying raw value fallback for `Result` without error closure |
| **`E0720`** | `UnusedFallibleResultError` | Discarding fallible `Result` without inspection |
| **`E0810`** | `CallFamilyViolationError` | Crossing disjoint runtime `fn` and compile-time `meta`/`type` call families |
| **`E0811`** | `CompileTimeBudgetExceededError` | Exhausting evaluation step budget in meta/type functions |
| **`E0812`** | `MetaTypeReturnProhibitedError` | 'meta fn' attempting to return 'type<...>' or sort 'Type'; type construction is monopolized by type functions |
| **`E0813`** | `MetaComputationAnnotationError` | Declaring algebraic effects ('@Eff') or state capabilities ('&Cap') on a 'meta fn' signature |
| **`E0820`** | `TotalityViolationError` | Totality certification failed in `halt fn` (unbounded recursion/loop) |
| **`E0830`** | `MetaAssertionFailedError` | Compile-time `assert` condition evaluated to `false` in `meta` context |
| **`E0901`** | `BodyInDeclModuleError` | Supplying an implementation body, variable initializer, or mutable binding in a '.d.ril' declaration unit |
| **`E0902`** | `MissingBodyInStandardModuleError` | Omitting an implementation body from a function declared in a standard '.ril' module |
| **`E0907`** | `ForeignStructuralFieldPenetrationError` | Attempting to access fields, mutate, index, deconstruct, or instantiate an opaque external type |
