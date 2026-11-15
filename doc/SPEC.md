# The Ril Language Specification

**Version:** 0.2.0  
**Status:** Canonical Reference Specification  
**Format:** Code-First Normative Document  

---

## Document Conventions

This document defines Ril syntax, static semantics, access modes, state and provenance tracking, algebraic effects, abstract-machine execution, and diagnostic error codes.

- **Normative Force**: Grammar productions, rule tables, judgment premises, and inline code annotations (`-- OK`, `-- Error [EXXXX]`, `-- Panics`) are normative. **Must** and **must not** express requirements and prohibitions; **may** permits an alternative; **should** gives advisory guidance.
- **Fixtures vs. Complete Source**: Code blocks are independent fixtures unless marked as complete source files. Abbreviated named callables in independent fixtures denote their compiler-completed signatures under [mandatory contract completion](#mandatory-contract-inference-and-completion) unless testing missing annotations (`E0510`, `E0544`, `E0612`). Complete source files spell all required operational-effect and state/provenance annotations.

| Distinction | Ril meaning |
| :--- | :--- |
| Binding / access | `let` and `var` govern slot replacement; default, `ref`, `mut`, `^mut`, and `new` govern path access and authority |
| Values / shared objects | `bool`, `int`, `f64`, `str`, `bytes`, and `()` copy by value; records, nonempty tuples, collections, and sums have GC-managed identity |
| Record forms / constructors | Named and anonymous records attach `.{...}` (`User.{ id: 1 }`); variant and non-record nominal constructors separate their payload with whitespace (`Ok 42`, `Ok ()`, `Some .{ x: 1 }`) |
| Upper-bound authority | Declared parameter/local mutability and state annotations are sound upper bounds; missing required authority fails (`E0510`, `E0520`), while unused excess capacity is permitted |
| Purity / defects | Purity excludes outward operational effects and non-pure state/provenance obligations; finite defects initiate LIFO panic unwinding |

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
    - [Failure Model and Purity](#failure-model-and-purity)
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
    - [Array, Map, Set, and Tuple Types](#array-map-set-and-tuple-types)
    - [Sum Types and Variant Spreading](#sum-types-and-variant-spreading)
      - [Sum Variant Spreading and Subset Conversion](#sum-variant-spreading-and-subset-conversion)
    - [Nominal, Opaque, and Resource Types](#nominal-opaque-and-resource-types)
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
    - [Generic Parameters and Value Sorts](#generic-parameters-and-value-sorts)
    - [Type Definition Boundaries](#type-definition-boundaries)
  - [Static Semantics and Type Kernel](#static-semantics-and-type-kernel)
    - [Static Contexts and Judgment Forms](#static-contexts-and-judgment-forms)
    - [Type Formation and Binding](#type-formation-and-binding)
    - [Definitional Equality and Recursive Types](#definitional-equality-and-recursive-types)
    - [Subtyping, Reception, and Contract Compatibility](#subtyping-reception-and-contract-compatibility)
    - [Bidirectional Expression Checking](#bidirectional-expression-checking)
    - [Structural Joins and Normal Continuations](#structural-joins-and-normal-continuations)
    - [Generic Evidence and Definition Checking](#generic-evidence-and-definition-checking)
    - [Authority, Calls, and Contract Operations](#authority-calls-and-contract-operations)
    - [Recursive Summaries and Grounded Inference](#recursive-summaries-and-grounded-inference)
    - [Phase Checking and Static Evaluation](#phase-checking-and-static-evaluation)
    - [Semantic Interfaces and Diagnostic Boundaries](#semantic-interfaces-and-diagnostic-boundaries)
  - [Declarations and Bindings](#declarations-and-bindings)
    - [Binding Modes and Storage Matrix](#binding-modes-and-storage-matrix)
      - [Sound Upper-Bound Authority](#sound-upper-bound-authority)
    - [Construction-Qualified Locals and Mode-Preserving Reception](#construction-qualified-locals-and-mode-preserving-reception)
    - [Immutable, Mutable, Shared, and Reference Bindings](#immutable-mutable-shared-and-reference-bindings)
    - [Scoped Resource Bindings](#scoped-resource-bindings)
    - [Declaration Metadata Attributes](#declaration-metadata-attributes)
    - [External Interface Declarations](#external-interface-declarations)
  - [Expressions and Operators](#expressions-and-operators)
    - [Expression Grammar and Precedence](#expression-grammar-and-precedence)
    - [Arithmetic, Bitwise, Relational, and Logical Operators](#arithmetic-bitwise-relational-and-logical-operators)
    - [Indexing, Slicing, and Static Coordinate Projection](#indexing-slicing-and-static-coordinate-projection)
    - [Text and Byte Operations](#text-and-byte-operations)
    - [Pipeline and Fallible Operators](#pipeline-and-fallible-operators)
    - [Record Construction and Assignments](#record-construction-and-assignments)
  - [Control Flow and Pattern Matching](#control-flow-and-pattern-matching)
    - [Block Expressions and Local Declarations](#block-expressions-and-local-declarations)
    - [Conditional and Loop Expressions](#conditional-and-loop-expressions)
    - [Guarded Bindings](#guarded-bindings)
    - [Pattern Matching](#pattern-matching)
  - [Functions, Closures, and Callables](#functions-closures-and-callables)
    - [Named Function Declarations and Contrast Matrix](#named-function-declarations-and-contrast-matrix)
    - [Callable Contracts](#callable-contracts)
      - [Mandatory Contract Inference and Completion](#mandatory-contract-inference-and-completion)
      - [Closed and Open Callable Rows](#closed-and-open-callable-rows)
      - [Callable Contract Matching](#callable-contract-matching)
    - [Return Construction, Access Modes, and Sources](#return-construction-access-modes-and-sources)
    - [Parameter Modes and Caller Obligations](#parameter-modes-and-caller-obligations)
    - [Anonymous Functions and Trailing Closures](#anonymous-functions-and-trailing-closures)
    - [Closures and Lexical Environments](#closures-and-lexical-environments)
  - [State and Provenance Tracking](#state-and-provenance-tracking)
    - [Local State Discharge, Parameter Mutation, and Sharing](#local-state-discharge-parameter-mutation-and-sharing)
    - [State Groups and Captured Layers](#state-groups-and-captured-layers)
    - [Exclusivity and Anti-Laundering Matrix](#exclusivity-and-anti-laundering-matrix)
  - [Algebraic Effects, Panic Containment, and Concurrency](#algebraic-effects-panic-containment-and-concurrency)
    - [Effect Declarations and Handlers](#effect-declarations-and-handlers)
    - [Built-in System Effects](#built-in-system-effects)
    - [Panic Absorption with absorb\_panic](#panic-absorption-with-absorb_panic)
    - [Structured Async Concurrency and Channels](#structured-async-concurrency-and-channels)
  - [Compile-Time Computation and Introspection](#compile-time-computation-and-introspection)
    - [Static Type Values and Type Quotation](#static-type-values-and-type-quotation)
    - [Pure Type Functions and Result Restrictions](#pure-type-functions-and-result-restrictions)
    - [Disjoint Call Families and Branch Pruning](#disjoint-call-families-and-branch-pruning)
    - [Static Introspection](#static-introspection)
    - [Structural Type Pattern Matching](#structural-type-pattern-matching)
  - [Modules, Program Execution, and Prelude](#modules-program-execution-and-prelude)
    - [Modules and Compilation Units](#modules-and-compilation-units)
    - [Module Imports and Visibility](#module-imports-and-visibility)
    - [Program Entry Point](#program-entry-point)
    - [Prelude Scope](#prelude-scope)
      - [Built-in Foundational Operations](#built-in-foundational-operations)
    - [Mandatory Inspection of Fallible Results](#mandatory-inspection-of-fallible-results)
  - [Diagnostic Error Codes Summary](#diagnostic-error-codes-summary)
    - [Source Text, Identifiers, and Syntax](#source-text-identifiers-and-syntax)
    - [Names, Initialization, and Field Identity](#names-initialization-and-field-identity)
    - [Types, Expressions, Generics, and Patterns](#types-expressions-generics-and-patterns)
    - [Parameters and Argument Modes](#parameters-and-argument-modes)
    - [Bindings, State, Access Modes, and Resource Contracts](#bindings-state-access-modes-and-resource-contracts)
    - [Effects, Concurrency, and Escape](#effects-concurrency-and-escape)
    - [Declaration Contexts, Control Flow, and Fallible Values](#declaration-contexts-control-flow-and-fallible-values)
    - [Static Computation](#static-computation)
    - [Module Forms, Entry Points, and External Contracts](#module-forms-entry-points-and-external-contracts)

---

## Notation, Abstract Machine, and Conformance

### Grammar Notation

Grammar productions use EBNF. Compact bracket expressions containing ranges, negation, or escapes denote lexical character classes; other `[ ... ]` forms denote optional syntax. `Newline` and `EOF` denote line end and source end.

```ebnf
Production  ::= Expression
Choice      ::= A | B
Sequence    ::= A B
Optional    ::= [ A ]
Repetition  ::= { A }
Terminal    ::= "literal" | 'literal'
Grouping    ::= ( A B )
```

```ril
let x = 42                             -- OK
-- let y: str = 42                     -- Error [E0301]: expected 'str', found 'int'
let arr = [1, 2]
-- let out = arr[5]                    -- Panics: index 5 out of bounds for length 2
```

### Program Conformance

A conforming Ril implementation must:
1. Accept all programs satisfying the syntactic grammar and static judgments within the configured static-evaluation budget.
2. Reject invalid programs with the diagnostic code assigned to each violated condition.
3. Preserve left-to-right operand evaluation, value/shared-object semantics, LIFO scope cleanup, and complete provenance checking across module interfaces.

### Diagnostic Classification

```ril
let valid_unused = 1                   -- OK
-- let bad_type: str = 1               -- Error [E0301]
-- let bad_div = 1 / 0                 -- Error [E0361]: constant zero divisor
meta fn static_ratio(d: int) -> int { 1 / d }
-- meta let Q = static_ratio(0)        -- Error [E0831]: panic during static evaluation
```

Specific diagnostics take precedence over general syntax (`E0120`) or type mismatch (`E0301`) codes (for example, `E0336` for an absent record field and `E0125` for a missing constructor space). Exact message wording is illustrative; error codes and triggering conditions are normative.

### Abstract Machine and Memory Semantics

Operands and call arguments evaluate strictly left-to-right; short-circuit operators (`&&`, `||`, `??`, `?.`, `?[`) and control transfers (`return`, `break`, `continue`, `?`) skip unevaluated operands.

```ril
let mut trace: []int = []
let mut log = \n: int -> { Array::push(mut trace, n); n }
let total = log(1) + log(2) * log(3)
assert(total == 7 && trace == [1, 2, 3])
```

| Memory property | Requirement |
| :--- | :--- |
| Automatic reclamation | Tracing GC reclaims unreachable shared-object graphs, including cycles, without running user code |
| Identity preservation | Moving GC preserves object identity, aliasing, and active `ref`/`mut`/`^mut` relationships |
| Authority independence | Object liveness grants no write authority; `let scoped` deterministic cleanup is independent of GC |

### Failure Model and Purity

<a id="termination-and-halt-contracts"></a>

Ril separates expected domain failures from programming defects:

1. **Recoverable Errors (`Result<T, E>` and `?T`)**: Carried as explicit values. Every `Result` must be inspected, propagated via `?`, or handled via `??` (`E0720`).
2. **Defects (`panic` / `assert`)**: Trigger deterministic LIFO stack unwinding, running active `let scoped` `close` handlers without requiring signature annotations. Unwind-safe boundaries (`absorb_panic`, `Async::supervise`) convert panics into `Result` values carrying `PanicInfo`.
3. **Purity**: A callable is pure when its normalized outward operational-effect row is empty (`@{}`) and its outward state/provenance obligations reduce to empty (`&{}`) after local discharge. `never` denotes computations with no normal continuation.

```ril
fn parse_port(s: str) -> Result<int, str> {
    if s == "" { Err "empty port" } else { Ok 8080 }
}

fn connect_port(raw: str) -> Result<int, str> {
    let port = parse_port(raw)?        -- OK: propagates Err
    Ok port
}
-- parse_port("80")                    -- Error [E0720]: unused Result
```

### Run-Time Failure Conditions

| Condition | Outcome |
| :--- | :--- |
| Integer `/ 0` or `% 0` (non-constant divisor) | LIFO panic unwinding (`"division by zero"`) |
| Bit shift `x << k` or `x >> k` with `k < 0` (non-constant `k`) | LIFO panic unwinding (`"negative shift count"`) |
| Out-of-bounds array/byte index `xs[i]` or slice `xs[a..b]` | LIFO panic unwinding |
| `panic(msg)` or false `assert(cond)` | LIFO panic unwinding |
| Secondary panic inside `let scoped` `close` during active panic/cancel unwinding | Immediate Double-Fault OS process termination (bypasses `absorb_panic`) |
| Unrecoverable host memory or call-stack exhaustion | Immediate OS process termination |

---

## Source Text and Lexical Elements

### Character Set and Encoding

Source files must be valid UTF-8 (`E0104` on ill-formed UTF-8 or BOM). Disallowed control characters (U+0000..U+001F except Tab U+0009, LF U+000A, CR U+000D; plus U+007F and bidirectional override controls U+202A..U+202E, U+2066..U+2069) outside literals/comments are rejected with `E0105`. CRLF (`\r\n`) normalizes to LF (`\n`).

### Comments

```ebnf
LineComment  ::= "--" { SourceChar } Newline
BlockComment ::= "{-" { SourceChar | BlockComment } "-}"
```

```ril
-- Invalid UTF-8 byte sequence or UTF-8 BOM at file start -> Error [E0104]
-- Control character U+0007 or bidi override outside literal -> Error [E0105]
-- {- unterminated block comment                          -> Error [E0106]
```

### Whitespace and Layout Rules

Spaces (` `) and horizontal tabs (`\t`) separate tokens. Newlines terminate statements (`Separator`) when the preceding token can end a statement and the next token is not a continuation token:

- **Line continues** after binary/pipeline/fallback operators (`+`, `-`, `*`, `/`, `%`, `&`, `|`, `^`, `<<`, `>>`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `&&`, `||`, `|>`, `??`, `=`, `+=`, `-=`, `*=`, `/=`, `%=`, `&=`, `|=`, `^=`, `<<=`, `>>=`, `->`, `:`, `,`, `.`, `?.`, `::`) or inside unclosed `( ... )`, `[ ... ]`, `.{ ... }`.
- **Line continues** before postfix `.field`, `?.field`, `|>`, or `??` on the next line.
- **Tight lexical attachment**: Call `(` (`f(x)`), index `[` (`xs[i]`, `xs?[i]`), and named record `.{` (`User.{ id: 1 }`) must attach with no intervening newline (`(` or `[` after a newline starts a new expression statement).

### Syntactic Diagnostic Conditions

| Code | Triggering condition |
| :---: | :--- |
| `E0120` | Unexpected token in the current syntactic production |
| `E0121` | Unexpected `EOF` while a construct remains incomplete |
| `E0122` | Unclosed `(`, `[`, `{`, `.{`, or committed `<` delimiter |
| `E0123` | Mismatched closing delimiter (`)`, `]`, `}`) |
| `E0124` | Omitted mandatory delimiter or separator token (`->`, `=`, `:`) |
| `E0125` | Variant or non-record nominal constructor directly followed by `(` without separating whitespace (`Ok(42)`, `Ok()`) |

```ril
type Res { Ok int, Ready }
let a = Ok 42                          -- OK
let b = Ready                          -- OK
-- let bad_tok = @                     -- Error [E0120]: unexpected token
-- let bad_eof = 1 +                   -- Error [E0121]: unexpected EOF
-- let bad_open = (1 + 2               -- Error [E0122]: unclosed '('
-- let bad_mismatch = [1, 2)           -- Error [E0123]: mismatched delimiter ')'
-- fn bad_sep(x int) -> int { x }      -- Error [E0124]: missing ':'
-- let bad1 = Ok(42)                   -- Error [E0125]: separate constructor and payload with whitespace ('Ok 42')
-- let bad2 = Ok()                     -- Error [E0125]: write 'Ok ()' for unit payload or bare 'Ready' for unit variant
```

### Identifiers and Casing Invariants

Ril enforces lexically disjoint ASCII identifier casing roles (`E0101` on wrong role, `E0102` on malformed mixed casing such as `camelCase` or leading/trailing/double underscores outside `_foo`):

```ebnf
Identifier         ::= PascalCase | ValueName | Wildcard
ValueName          ::= SnakeCase | ScreamingSnakeCase | UnderscoreName
PascalCase         ::= [A-Z] { [a-z0-9] } { [A-Z] { [a-z0-9] } }
SnakeCase          ::= [a-z] { [a-z0-9] } { "_" [a-z0-9]+ }
ScreamingSnakeCase ::= [A-Z] { "_" [A-Z0-9]+ }
                     | [A-Z] [A-Z0-9]+ { "_" [A-Z0-9]+ }
UnderscoreName     ::= "_" [a-z0-9]+ { "_" [a-z0-9]+ }
Wildcard           ::= "_"
QualifiedName      ::= { PascalCase "::" } Identifier
```

- **Disjoint Partition between `PascalCase` and `ScreamingSnakeCase` (`E0101`, `E0102`)**:
  - `PascalCase` starts with `[A-Z]`, contains no `_`, and must include at least one lowercase letter `[a-z]` whenever its length is $\ge 2$ (`U`, `T`, `User`, `UserId`, `UserID`, `HTTPServer`, `JSONParser`, `Sha256` are valid `PascalCase`; multi-letter all-uppercase names without lowercase letters such as `PI`, `OS`, `TABLE`, `MAX_CONN` are exclusively `ScreamingSnakeCase` constants!).
  - Single-letter uppercase names (`T`, `U`, `K`, `V`, `M`) are `PascalCase` type/mode/variant identifiers; constants use $\ge 2$ characters (`PI`, `N_MAX`) or `snake_case`.
- **Roles (`E0101`)**:
  - `PascalCase`: Types, sum variants, effects (`eff`), module aliases, type/mode generic parameters.
  - `ValueName` (`SnakeCase` / `ScreamingSnakeCase` / `UnderscoreName`): Functions, parameters, local/top-level value and `meta let` bindings, record fields, effect operations, const generic parameters.
  - `Wildcard` (`_`): Discard binder/pattern only; reading `_` as a value expression fails `E0322`.
- **Name Resolution (`E0103`, `E0203`, `E0204`, `E0206`)**:
  - Same-scope duplicate declarations fail `E0203` (`Type` is a protected intrinsic name and cannot be redeclared, `E0203`).
  - Unresolved names fail `E0204`. Unqualified variant constructors imported or declared from multiple sums in the same scope fail `E0206` unless qualified (`SumA::Tag`). A `PascalCase` identifier in a binding position where a variable binder is required fails `E0103`.

```ril
type HTTPServer = .{ port: int }       -- OK: mixed-case acronym PascalCase
let sha_256 = "digest"                 -- OK: digits permitted after '_' in snake_case
let MAX_RETRY = 3                      -- OK: ScreamingSnakeCase constant
-- let badCamel = 1                    -- Error [E0102]: mixed camelCase prohibited
-- type Bad_Type = int                 -- Error [E0102]: '_' prohibited in PascalCase
-- type TABLE = int                    -- Error [E0101]: all-caps 'TABLE' is ScreamingSnakeCase, not PascalCase
-- let BadVar = 10                     -- Error [E0103]: PascalCase in variable binding position
-- let MAX_RETRY = 4                   -- Error [E0203]: duplicate declaration in same scope
-- let ghost = missing_name            -- Error [E0204]: unresolved identifier
-- type A { Dup }; type B { Dup }
-- let ambig = Dup                     -- Error [E0206]: ambiguous unqualified constructor; write 'A::Dup'
-- let _ = 1; let bad_wild = _         -- Error [E0322]: '_' cannot be read as an expression
-- let return = 1                      -- Error [E0113]: reserved keyword used as identifier
```

### Keywords

Reserved keywords cannot be used as identifiers (`E0113`):

```text
as       break    close    continue eff      else     false    fn
for      if       infer    let      loop     match    meta     mut
never    new      opaque   pkg      pub      ref      resource return
scoped   true     type     typeof   use      var      via      while
with
```

Primitive type names (`bool`, `int`, `f64`, `str`, `bytes`) are predeclared type identifiers in the language prelude (`Type` is protected).

### Numeric Literals

Ril provides two numeric types: arbitrary-precision signed `int` and IEEE-754 binary64 `f64`. Numeric literals carry no width suffixes (`E0111` on malformed digits, trailing `_`, or invalid suffixes; `E0326` on `f64` literal magnitude overflow beyond finite binary64).

```ebnf
IntLiteral     ::= DecimalLiteral | HexLiteral | OctalLiteral | BinaryLiteral
DecimalLiteral ::= Digit { [ "_" ] Digit }
HexLiteral     ::= "0" ( "x" | "X" ) HexDigit { [ "_" ] HexDigit }
OctalLiteral   ::= "0" ( "o" | "O" ) OctalDigit { [ "_" ] OctalDigit }
BinaryLiteral  ::= "0" ( "b" | "B" ) BinaryDigit { [ "_" ] BinaryDigit }
FloatLiteral   ::= DecimalLiteral "." DecimalLiteral [ Exponent ]
                 | DecimalLiteral Exponent
Exponent       ::= ( "e" | "E" ) [ "+" | "-" ] DecimalLiteral
Digit          ::= [0-9]
HexDigit       ::= [0-9a-fA-F]
OctalDigit     ::= [0-7]
BinaryDigit    ::= [0-1]
```

```ril
let big = 1_000_000_000_000_000_000_000_000_000_000
let mask = 0xFF_00
let ratio = 3.14159e-2
-- let bad_hex = 0x                    -- Error [E0111]
-- let bad_suf = 42u8                  -- Error [E0111]: numeric suffixes are not supported
-- let bad_inf = 1.0e999               -- Error [E0326]: f64 literal overflows finite binary64 range
```

### Text and Byte Literals

`str` literals hold valid UTF-8 scalar sequences; `bytes` literals hold immutable byte sequences (`0..=255`). Interpolations `"{expr}"` inside `StringLiteral` accept `str`, `int`, `f64`, and `bool` expressions directly (`E0301` on other types; `E0112` on empty `{}` or malformed braces; `{{` and `}}` escape literal braces).

```ebnf
StringLiteral     ::= '"' { StringCharacter | EscapeSequence | Interpolation } '"'
RawStringLiteral  ::= 'r"' { RawCharacter } '"'
ByteStringLiteral ::= 'bytes"' { ByteCharacter | ByteEscape } '"'
RawByteLiteral    ::= 'rbytes"' { RawByteCharacter } '"'
Interpolation     ::= "{" Expression "}"
```

- **String escapes (`E0108`, `E0109`, `E0107`)**: `\\`, `\"`, `\n`, `\r`, `\t`, `\0`, `\{`, `\}`, and `\u{H+}` (1–6 hex digits denoting a valid Unicode scalar value, `E0109` on surrogates or `> 0x10FFFF`).
- **Byte escapes (`E0110`)**: ASCII `0x20..0x7E` (excluding unescaped `"` and `\`) plus `\\`, `\"`, `\n`, `\r`, `\t`, `\0`, and `\xHH` (exact 2 hex digits). Non-ASCII characters in `bytes"..."` / `rbytes"..."` fail `E0110`.

```ril
let host = "ril.dev"
let port = 443
let url = "https://{host}:{port}/v1"
let raw = r"C:\data\ril"
let magic = bytes"\x89PNG\r\n\x1a\n"
assert(url == "https://ril.dev:443/v1" && len(magic) == 8)
-- let bad_unterm = "unterminated      -- Error [E0107]
-- let bad_esc = "\q"                  -- Error [E0108]: unknown escape
-- let bad_uni = "\u{D800}"            -- Error [E0109]: UTF-16 surrogate is not a Unicode scalar
-- let bad_byte = bytes"λ"             -- Error [E0110]: non-ASCII byte literal character
-- let bad_interp = "val={}"           -- Error [E0112]: empty interpolation expression
```

### Boolean and Unit Literals

```ebnf
Literal ::= IntLiteral | FloatLiteral | StringLiteral | RawStringLiteral
          | ByteStringLiteral | RawByteLiteral | "true" | "false" | "(" ")"
```

---

## Types and Memory Model

```ebnf
PrimitiveType  ::= "bool" | "int" | "f64" | "str" | "bytes" | "never"
TypeExpression ::= PrimaryType
                 | RecordType
                 | TupleType
                 | ArrayType
                 | MapType
                 | CallableType
                 | TypeProjection
                 | TypeFunctionExpr
                 | "?" TypeExpression
                 | "typeof" Expression
                 | MappedRecordType
PrimaryType    ::= PrimitiveType
                 | TypeReference
                 | TokenType
                 | "(" TypeExpression ")"
                 | "<" Expression ">"
TypeReference  ::= QualifiedName [ GenericArgs ]
```

### Value Types

`bool`, `int`, `f64`, `str`, `bytes`, `()`, and `never` have no object identity and copy logically by value (implementations may share immutable backing buffers transparently). Value types forbid `ref`, `mut`, and `^mut` access modes in bindings, record fields, collection elements (`E0402`), and parameters (`E0401`).

```ril
let a = "hello"
let b = a                              -- Value copy
-- let ref bad_ref = a                 -- Error [E0402]: value type 'str' forbids 'ref'
-- fn bad_param(mut n: int) -> () {}   -- Error [E0401]: value type 'int' forbids 'mut' parameter
```

### Shared Object Types

Records (`.{...}`), nonempty tuples `(A, B)`, arrays `[M]T`, maps `[K: M V]`, `Set<T>`, and sum instances have heap allocation identity managed by tracing GC. Shared-object status permits aliasing of immutable snapshots (`let`) and explicit shared write handles (`^mut`), never implicit shared mutation.

### Record Types and Row Polymorphism

Record types, values, patterns, and mapped types uniformly use `.{...}`. Record fields may declare slot/access `MemberMode` modifiers (`var`, `mut`, `^mut`, `ref`, `var mut`, `var ^mut`, `var ref`).

```ebnf
RecordType      ::= ".{" [ RecordFieldList ] "}"
RecordFieldList ::= RecordTail
                  | RecordField { "," RecordField } [ "," RecordTail ] [ "," ]
RecordField     ::= { MetaAttr } [ MemberMode ] FieldLabel ":" TypeExpression
FieldLabel      ::= ValueName
RecordTail      ::= ".." [ PascalCase ]
MemberMode      ::= "var" [ "mut" | "^mut" | "ref" ]
                  | "mut" | "^mut" | "ref"
```

- **Closed Records**: Exact field set (written order irrelevant). Duplicate labels fail `E0210`; missing fields fail `E0307`; unexpected fields fail `E0302`; reading an unknown field fails `E0336`; dynamic bracket indexing `rec[k]` fails `E0324`.
- **Row Polymorphism (`..R` / `..`)**: Opens a record type in generic bounds or type aliases (`type WithId<R> = .{ id: int, ..R }`). Non-record row instantiations fail `E0306`; overlapping explicit labels and row remainder labels fail `E0212`. Incompatible field modes fail `E0357`.

```ril
type WithId<R> = .{ id: int, ..R }
type User = WithId<.{ var name: str, mut tags: []str }>

fn get_id<T: .{ id: int, .. }>(item: T) -> int { item.id }
let u = .{ id: 7, active: true }
assert(get_id(u) == 7)
-- type BadDup = .{ id: int, id: int }          -- Error [E0210]: duplicate field label
-- type BadOverlap = WithId<.{ id: str }>       -- Error [E0212]: row remainder overlaps 'id'
-- type BadTail = WithId<int>                   -- Error [E0306]: row tail requires a record type
-- let bad_extra: .{ id: int } = .{ id: 1, x: 2 } -- Error [E0302]: unexpected field 'x'
-- let bad_miss: .{ id: int, x: int } = .{ id: 1 } -- Error [E0307]: missing field 'x'
-- let bad_unknown = u.email                    -- Error [E0336]: unknown field 'email'
-- let bad_dyn = u["id"]                        -- Error [E0324]: dynamic bracket indexing prohibited on records
-- let bad_mode: .{ var x: int } = .{ x: 1 }    -- Error [E0357]: incompatible member mode
```

### Array, Map, Set, and Tuple Types

```ebnf
ArrayType             ::= "[" [ ElementAccessMode ] "]" TypeExpression
ElementAccessMode     ::= "mut" | "^mut" | "ref" | "via" | StorageModeExpression
StorageModeExpression ::= PascalCase | QualifiedName
MapType               ::= "[" TypeExpression ":" [ ElementAccessMode ] TypeExpression "]"
TupleType             ::= "(" ")"
                        | "(" TypeExpression "," TypeExpression { "," TypeExpression } [ "," ] ")"
```

- **Arrays & Maps**: Default element mode is deeply immutable (`[]T`, `[K: V]`). Element modes admit `mut`, `^mut`, `ref`, `via`, or `MemberMode` parameters without `var` slot modifiers (`E0356`). Map keys `K` and `Set<T>` elements must support structural value equality (`E0328`). Collection lengths and indices have type `int`.
- **Tuples**: Zero-element `()` or $\ge 2$ elements `(A, B)`. Single-element `(T)` is grouping, never a 1-tuple. Tuple slots are strictly immutable; mutable multi-field aggregates use records (`.{ var a: A, mut b: B }`). Out-of-bounds tuple projection `pair.5` fails `E0312`.

```ril
let xs: []int = [10, 20, 30]
let mut table: [str: int] = ["ok": 200]
table["not_found"] = 404
let pair: (int, str) = (1, "one")
assert(xs[0] == 10 && table["ok"] == 200 && pair.1 == "one")
-- let bad_idx = pair.2                -- Error [E0312]: tuple index out of bounds
-- type BadKey = [f64: int]            -- Error [E0328]: 'f64' is not a valid map/set key type
-- type BadElem = [var][]int           -- Error [E0356]: array element mode forbids 'var'
```

### Sum Types and Variant Spreading

Every sum variant declares either no payload (unit tag) or **one** payload type (`T`, `(A, B)`, `.{...}`, `[]T`, etc.).

```ebnf
SumTypeDecl     ::= { MetaAttr } [ Visibility ] [ "opaque" ] "type" PascalCase [ GenericParams ]
                    "{" VariantDeclList "}" [ CloseClause ]
VariantDeclList ::= VariantDeclItem { "," VariantDeclItem } [ "," ]
VariantDeclItem ::= VariantSpread | VariantDecl
VariantSpread   ::= ".." TypeReference
VariantDecl     ::= { MetaAttr } PascalCase [ TypeExpression ]
                  | ".."
CloseClause     ::= "close" SnakeCase
```

- **Construction & First-Class Constructors**: Unit variants evaluate directly (`None`, `Pending`). Payload variants take one space-separated argument (`Ok 42`, `Ok ()`, `Pair (1, 2)`, `Node .{ id: 1 }`). A bare payload-variant name in value position has function type `fn(Payload) -> Sum` (`42 |> Ok`).
- **Open Extensible Sums (`..`)**: Trailing `..` marks a sum open to future variants outside its defining `pkg`, requiring a wildcard `_` arm in external `match` expressions (`E0303`).

```ril
pub type Shape {
    Origin,
    Circle f64,
    Rect (f64, f64),
    Polygon .{ vertices: [](f64, f64), closed: bool },
}

let s1 = Shape::Origin
let s2 = Shape::Circle 5.0
let s3 = Shape::Rect (10.0, 20.0)
let s4 = Shape::Polygon .{ vertices: [(0.0, 0.0)], closed: true }
let wrapped: ?int = 99 |> Some
assert(wrapped == Some 99)
```

#### Sum Variant Spreading and Subset Conversion

`..SubType` splices another accessible transparent sum's variants into a superset sum (`E0306` on non-sum, `E0308` on sealed/open sum, `E0313` on spread cycles, `E0213` on conflicting payload types for the same variant tag; identical variant tags with definitionally equal payloads deduplicate cleanly). This establishes static sum inclusion $Sub \preceq_{\text{sum}} Sup$:

1. **Postfix `?` Automatic Widening**: Inside a function returning `Result<T, Sup>`, `sub_res?` widens `Err sub_err` to `Sup` automatically when $Sub \preceq_{\text{sum}} Sup$.
2. **Explicit Widening (`expr as SupType`)**: Re-wraps a `Sub` value into `Sup` when $Sub \preceq_{\text{sum}} Sup$ (`E0301` otherwise).
3. **Pattern Subset Narrowing (`SubType as binder` / `SubType as _`)**: Matches any variant belonging to `SubType` and binds the narrowed `SubType` value.

```ril
pub type DbErr { Deadlock, ConnLost str }
pub type AuthErr { MissingToken, Expired }
pub type ApiErr { ..DbErr, ..AuthErr, BadInput str }
-- type ConflictErr { ..DbErr, ConnLost int } -- Error [E0213]: conflicting payload for 'ConnLost'

fn handle_err(err: ApiErr) -> (int, str) {
    match err {
        DbErr as db    -> (503, match db { Deadlock -> "retry", ConnLost h -> h }),
        AuthErr as _   -> (401, "unauthorized"),
        BadInput field -> (400, field),
    }
}

fn widen_demo(e: DbErr) -> ApiErr {
    e as ApiErr                        -- OK: DbErr <= ApiErr
}
```

| Source authority of `e` | Subset re-wrap (`Sub as x` / `e as Sup`) provenance rule |
| :--- | :--- |
| Deeply immutable `e`, or target sum has only immutable/value payloads | Produces an ordinary deeply immutable value |
| Construction `new` | Consumes source path on match/widen (`E0549`); produces `new` target sum |
| Shared writable `^mut` with mutable payload members | Requires `^mut` marker (`Sub as ^mut x` / `(^mut e) as Sup`, `E0510`); returning records `&return{^mut src}` |
| Borrowed `ref` / `mut` with live/mutable payload members | Temporary scoped observation/access bounded by source lifetime; persistent `let ref` (`E0543`) and root `-> ref(src)` (`E0545`) are prohibited; contained return records `&return{ref src}` |

### Nominal, Opaque, and Resource Types

Ril defines four `.ril` type declaration forms plus `.d.ril` `resource` handles:

```ebnf
TypeDecl       ::= [ Visibility ] "type" PascalCase [ GenericParams ] "=" TypeExpression
OpaqueTypeDecl ::= { MetaAttr } [ Visibility ] "opaque" "type" PascalCase [ GenericParams ]
                   "=" TypeExpression [ CloseClause ]
NominalDecl    ::= { MetaAttr } [ Visibility ] [ "opaque" ] "type" PascalCase [ GenericParams ]
                   [ TypeExpression ] [ CloseClause ]
LocalTypeDecl  ::= TypeDecl | OpaqueTypeDecl | NominalDecl | SumTypeDecl
```

| Form | Declaration | Identity & construction |
| :--- | :--- | :--- |
| Transparent alias | `type Point = .{ x: f64, y: f64 }` | `=` makes it definitionally equal to its target everywhere (`E0313` on alias cycles) |
| Module-opaque type | `pub opaque type Token = str` | Transparent inside its defining module; distinct sealed type outside (`E0301` / `E0308`) |
| Nominal type / marker | `pub type Marker`<br>`pub type UserId int`<br>`pub type Tag .{ k: str }` | No `=`: distinct type everywhere (`E0305`). Unit `Marker` is a value; non-record `UserId 42` uses space; nominal record `Tag.{ k: "a" }` attaches `.{` |
| Sum type | `pub type Res<T, E> { Ok T, Err E }` | Tagged union (`opaque` seals variant construction/matching outside defining module, `E0308`) |
| Foreign affine resource (`.d.ril` only) | `pub resource type OwnedFd close close_fd` | Exclusive affine handle: forbids `clone`, `derive`, `==`, plain `let` snapshot freezing, `^mut` sharing, and heap `[M]` arrays; admits `new` creation/consumption, `let mut`, `mut`, `ref`, and `let scoped mut` |

Compile-time state machines combine unit nominal markers, phantom type parameters on `opaque type`, and `new` handoff (`E0549` ends the old state binding on transition):

```ril
pub type Disconnected
pub type Connected
pub type UserId int
pub type OrgId int
pub opaque type Conn<State> = .{ fd: int }

pub fn open_raw() -> new Conn<Disconnected> { Conn.{ fd: -1 } }
pub fn dial(new c: Conn<Disconnected>, fd: int) -> new Conn<Connected> {
    Conn.{ fd: c.fd + fd + 1 }
}

let mut c0 = open_raw()
let mut c1 = dial(new c0, 3)
-- let _ = dial(new c0, 4)             -- Error [E0549]: 'c0' ended at handoff
-- let bad_nom: OrgId = UserId 1       -- Error [E0305]: distinct nominal types 'OrgId' vs 'UserId'
-- type Cyc = Cyc                      -- Error [E0313]: cyclic transparent type alias
-- Outside Conn's module:
-- let bad_peek = c1.fd                -- Error [E0308]: opaque representation is sealed outside defining module
```

### Deep Immutability

Plain `let`, `var`, default parameters, and plain collection elements hold **deeply immutable snapshots**: no surviving writable alias (`mut` / `^mut`) and no live `ref` dependency may reach the stored graph (`E0535`). When an immutable value is received for a schema containing `var`/`mut`/`ref` members, those member modes remain inactive on the frozen snapshot (`E0520` on write).

`clone(value)` / `clone(ref live)` deep-copies any ordinary `SharedObject` graph (preserving internal aliasing and cycles within the copied graph) into an isolated `new T` (`E0301` on value types, `resource` handles, or callables; `E0530` when containing non-clonable live/mutable closure environments).

```ril
type Cell = .{ var count: int }
let mut live = Cell.{ count: 1 }
-- let bad_snap = live                 -- Error [E0535]: 'live' has surviving write authority
let snap = clone(ref live)             -- OK: isolated snapshot frozen into 'let'
let mut copy = clone(snap)             -- OK: 'clone' returns isolated 'new Cell'
copy.count = 99
assert(live.count == 1 && snap.count == 1 && copy.count == 99)
let ^mut shared = live
let mut holder = .{ cb: \-> { shared.count += 1; shared.count } }
-- let _ = clone(ref holder)           -- Error [E0530]: cannot clone structure holding mutable closure authority
```

### Type Identity and Subtyping

Ril has **no implicit numeric widening** and **no structural width subtyping** on closed records (`E0301`). Subtyping $S <: T$ holds only for:
1. Reflexivity / definitional equality ($S \equiv T$, expanding transparent `type A = B` aliases).
2. Bottom type (`never <: T` for every well-formed `T`).
3. Covariant immutable optionals (`?S <: ?T` when $S <: T$; mutable/invariant containers require `S ≡ T`).
4. Callable contract subsumption (`MatchCallable`: contravariant parameter types, covariant return type, identical concrete access modes, and bounded effect/state rows).

### Complete Provenance and Required Annotations

Access modes, origins, state writes, environment captures, and effects are static judgments verified modularly across call boundaries and erased before code generation. Named functions spell their required operational effects (`@Eff`) and non-pure state/provenance clauses (`&mut`, `&^mut`, `&capture`, `&up{...}`, `&return{...}`); anonymous closures infer full contracts automatically.

### Access Mode Inference with via and infer

`via` binds static access-mode parameters over parameter/member schemas; `-> infer T` derives the return mode (`plain`, `ref(...)`, `^mut(...)`, `new`) and `&return{...}` provenance from the checked body while keeping data type `T` explicit. Writing `-> infer T` or `let via` without an explicit `via` parameter in that callable's own parameter list fails `E0412`.

```ril
type Cell = .{ var count: int }

fn relay<T>(via item: T) -> infer T {
    let via local = item
    local
}

let plain = relay(Cell.{ count: 1 })
let mut live = Cell.{ count: 2 }
let ref view = relay(ref live)
let mut moved = relay(new live)
moved.count += 10
assert(plain.count == 1 && moved.count == 12)
-- fn bad_infer(x: Cell) -> infer Cell { x }    -- Error [E0412]: 'infer' requires 'via' parameter
-- fn bad_scalar(via n: int) -> int { n }       -- Error [E0550]: redundant 'via' on fixed scalar 'int'
-- Published interface: fn read(via c: Cell) -> int; narrowing to '&mut' breaks baseline -> Error [E0552]
```

#### Member Modes and Implicit Schema Parameters

`via` in composite parameter schemas (`[via]T`, `[K: via V]`, `.{ via item: T }`) binds an implicit static element/member mode parameter instantiated from the caller's argument schema. Each concrete storage allocation fixes its schema at creation; later writes check that fixed schema without changing its mode.

#### Inference Domains and Contract Completion

A `via x: T` parameter admits modes from `{plain, ref, mut, ^mut, new}` compatible with `T` and all body uses. Writing `via` on a concrete fixed-value scalar (`via n: int`) where only one mode can ever exist fails `E0550`. Inside a `via` function, concrete `&mut` / `&^mut` / `&return` clauses implied solely by `via` instantiations are recorded in the inferred template interface automatically without requiring redundant source spelling on the `via` function header.

#### Preserving Reception and Forwarding

Within a lexical `via` template, `let via y = expr` preserves the exact instantiated access mode and construction/origin provenance of a `via`-dependent expression (`E0550` if `expr` has a fixed non-dependent mode). Concrete calls to non-`via` parameters still require explicit `mut` / `ref` / `^mut` / `new` argument markers (`E0405`).

#### Lexical Mode Templates and Closures

Closures inside a `via` function may reference enclosing `via` bindings; captured schemas and `-> infer` contracts specialize per outer mode instantiation while enforcing standard capture, lifetime, and affine `new` consumption rules.

#### Inferred Interfaces and Callable Families

In higher-order parameter types, `fn(via T) @& -> infer R` opens mode polymorphism independently of `@&` effect/state openness. Exported `via` functions retain normalized mode-to-contract summaries in module metadata; narrowing accepted modes or weakening result guarantees against a published interface baseline fails `E0552`.

### Functional Updates via Derive

`derive(base, \mut draft -> { ... })` (typically piped as `base |> derive \mut draft -> { ... }`) performs path-targeted updates on a deeply immutable `SharedObject` snapshot using structural sharing, returning a new deeply immutable `T`.

```ril
type Profile = .{ email: str, tags: []str }
type Account = .{ id: int, profile: Profile }

let base = Account.{ id: 1, profile: Profile.{ email: "a@ril.dev", tags: ["core"] } }
let next = base |> derive \mut d -> {
    d.profile.email = "b@ril.dev"
    Array::push(mut d.profile.tags, "admin")
}
assert(base.profile.email == "a@ril.dev" && len(base.profile.tags) == 1)
assert(next.profile.email == "b@ril.dev" && next.profile.tags == ["core", "admin"])
-- let _ = 42 |> derive \mut _d -> ()            -- Error [E0536]: value type 'int' is not a SharedObject
-- var leak: ?(fn() &up -> str) = None
-- let _ = base |> derive \mut d -> { leak = Some \-> d.profile.email } -- Error [E0607]: Draft escapes recipe
```

| `derive` rule | Requirement |
| :--- | :--- |
| Root eligibility (`E0536`) | `base` must be a deeply immutable `SharedObject` (including accessible `opaque`/nominal shared objects); value types, `resource` handles, and live `mut`/`^mut`/`ref` roots fail `E0536` |
| `Draft<T>` confinement (`E0607`) | `Draft<T>` is bound to the recipe activation; draft handles, derived `ref`/`mut` paths, and capturing closures cannot escape the recipe (`E0607`) |
| Inserted values (`E0535`) | Assigned values must be deeply immutable or recipe-local fresh allocations free of external surviving writers (`E0535`) |
| Fixed shape (`E0336`, `E0312`) | Preserves record fields, tuple arity, and sum tags of `T`; forwards recipe operational effects and external state obligations |

### Generic Parameters and Value Sorts

<a id="generic-parameters-defaults-and-value-sorts"></a>

Declarations admit rigid type parameters (`T`), compile-time value parameters (`cap: int`), and member-mode parameters (`M: MemberMode`), without default generic arguments.

```ebnf
GenericParams         ::= "<" GenericParamDecl { "," GenericParamDecl } [ "," ] ">"
GenericParamDecl      ::= TypeParamDecl | ConstParamDecl | ModeParamDecl
TypeParamDecl         ::= PascalCase [ TypeConstraint ]
TypeConstraint        ::= [ ":" TypeSort ] { "|>" PipelineConstraint }
TypeSort              ::= TypeSetSort | "Type" | RecordConstraint
TypeSetSort           ::= TypeReference "|" TypeReference { "|" TypeReference }
PipelineConstraint    ::= QualifiedName [ GenericArgs ]
ConstParamDecl        ::= ValueName ":" TypeExpression { "|>" PipelineConstraint }
RecordConstraint      ::= ".{" RecordConstraintField { "," RecordConstraintField } "," RecordTail "}"
                        | ".{" RecordTail "}"
RecordConstraintField ::= [ MemberMode ] FieldLabel ":" TypeExpression
ModeParamDecl         ::= PascalCase ":" ModeSortReference
ModeSortReference     ::= [ "ril/reflect::" ] "MemberMode"
GenericArgs           ::= "<" GenericArg { "," GenericArg } [ "," ] ">"
GenericArg            ::= TypeExpression | Expression | MemberModeLiteral
MemberModeLiteral     ::= "var" [ "mut" | "^mut" | "ref" ] | "mut" | "^mut" | "ref"
```

- **Closed Type Sets (`T: int | f64`, `E0301`, `E0304`, `E0306`, `E0318`)**: Restricts `T` to a finite set of rigid types; every member is checked at the definition site (`E0301`), each call specializes `T` to one rigid type (`E0306` if unspecialized), and `match <T>` covering all set members is exhaustive (`E0304` on redundant `_`). Untagged unions or literal values as storage types fail `E0318`.
- **Pipeline Guards (`T |> Guard`, `E0301`, `E0306`)**: `Guard` must be a pure type function; `T` satisfies `Guard` iff $T \not\equiv \text{never} \wedge \text{Guard}\langle T \rangle \equiv T$.
- **Strict Parameter Sorts (`E0306`, `E0323`, `E0814`, `E0340`, `E0344`)**: Ordinary values/tokens cannot supply type parameters (`E0306`; write `typeof e`). Wrong value sorts fail `E0323`; runtime values in const args fail `E0814`; wrong generic arity fails `E0340`; undetermined type/const parameters fail `E0344`. Type syntax adapts one-way to a declared `Type<T>` const parameter.

```ril
fn add<T: int | f64>(a: T, b: T) -> T { a + b }
assert(add(2, 3) == 5 && add(1.5, 0.5) == 2.0)

type Positive = \n: int -> if n > 0 { <()> } else { <never> }
type FixedChunk<cap: int |> Positive> = .{ data: []int }
type ValidChunk = FixedChunk<64>
-- type BadChunk = FixedChunk<0>       -- Error [E0323]: fails guard 'Positive'
-- type BadSort = FixedChunk<int>      -- Error [E0323]: type supplied to const parameter
-- type BadUnion = int | str           -- Error [E0318]: untagged union cannot be used as storage type
-- type BadArity = Option<int, str>    -- Error [E0340]: generic arity mismatch
-- let bad_empty = []                  -- Error [E0344]: element type cannot be determined
-- fn dyn_cap(n: int) -> () { let _: FixedChunk<n> = .{ data: [] } } -- Error [E0814]: non-static const arg
```

### Type Definition Boundaries

Effects (`@Eff`), state clauses (`&mut`, `&up`), and open row markers (`@`, `&`, `@&`) belong exclusively on `CallableType` arrows and function declarations:

```ril
-- type BadEff = @Io                   -- Error [E0330]: effect is not a data type
-- type BadState = &mut                -- Error [E0331]: state clause is not a data type
-- type BadVar { Run @Io }             -- Error [E0332]: effect suffix on sum variant
-- type BadFld = .{ x: int @Io }       -- Error [E0333]: effect suffix on non-callable field
-- type BadBnd<T: @Io> = T             -- Error [E0334]: effect bound on generic parameter
-- type BadTFn = \T @Io -> <T>         -- Error [E0335]: effect annotation on type function
-- let bad_val: str @Io = "hi"         -- Error [E0613]: effect annotation on value binding
```

| Invalid placement | Diagnostic |
| :--- | :---: |
| Bare `@Eff` or open `@` as a `TypeDecl` target | `E0330` |
| Bare `&mut` / `&up` or open `&` as a `TypeDecl` target | `E0331` |
| Effect or state suffix on a sum variant | `E0332` |
| Effect or state suffix directly on a non-callable record/tuple field | `E0333` |
| Effect or state bound on a generic parameter (`<T: @Io>`) | `E0334` |
| Effect or state annotation on a `TypeFunctionExpr` (`\T @Io -> <T>`) | `E0335` |
| Effect annotation on a value binding or array type (`let x: str @Io`) | `E0613` |

---

## Static Semantics and Type Kernel

### Static Contexts and Judgment Forms

```text
C = (D; Delta; Gamma; Phi; F; q)
J = (access, provenance, obligations, latent contracts, confinement, normal-successor flow)

C |- A : Type                         well-formed data type
C |- a : Static(S)                    static argument of sort S
C |- A equiv B                        definitional equality
C |- A <: B                           subtyping
C |- Receive(actual, receiver)        mode and provenance reception
C |- MatchCallable(actual, expected)  callable contract subsumption
C |- e => T ; J                       bidirectional synthesis
C |- e <= T ; J                       bidirectional checking
C |- e <= TypeResult ; J              type-producing result checking
```

| Context component | Contents |
| :--- | :--- |
| `D` | Package (`pkg`) and module scopes, visibility/opacity, type `close` contracts, primitive/foreign signatures |
| `Delta` | Rigid type, const, member-mode, and record-row parameters |
| `Gamma` | Value bindings, slot/access modes, callable contracts, lexical region tags ($\sigma$) |
| `Phi` | Declared generic constraints and static `match <T>` branch evidence |
| `F` | Origin sets, active construction paths (`new`), aliasing/exclusivity, `Result` inspection obligations |
| `q` | Phase: `TypeEval`, `MetaValue`, or `RunTime` |

### Type Formation and Binding

- **K-TYPE**: Primitives, rigid parameters in `Delta`, well-sorted generic applications, distinct-label records, arity-$0$ or $\ge 2$ immutable-slot tuples, valid-mode collections, complete `CallableType` contracts, `Type<A>`, and forward-evaluated computed types form valid types.
- **K-TYPE-ROW**: `.{ fields L, ..R }` is well-formed iff `R` instantiates to a record row whose labels are disjoint from `L` (`E0306` on non-record `R`, `E0212` on overlapping labels).

### Definitional Equality and Recursive Types

- **K-EQ**: Transparent `type A = B` aliases expand directly; cyclic transparent aliases without nominal or sum indirection fail `E0313`. Records compare equal up to field reordering when labels, types, and `MemberMode`s match. Nominal, sum, `opaque`, and `.d.ril` `resource` types compare by declaration identity and static argument equivalence (canonical IEEE bits for `f64` where `-0.0 != 0.0` and NaNs agree; structural value equivalence for collections/records; definitional target identity for `Type<A>`).
- **Opacity Scope**: Inside the defining `.ril` file, `opaque type A = Rep` permits representation projection and construction while retaining `A`'s declaration identity in `Type<A>` and exported interfaces; outside that file, `Rep` is sealed (`E0301`, `E0308`).

### Subtyping, Reception, and Contract Compatibility

- **K-RECV (`Receive`)**: Validates receiving an expression of synthesized mode/origins into a target binding, parameter, element, or return schema:
  - Plain immutable receivers require deeply immutable inputs free of surviving writers and live `ref` origins (`E0535`).
  - Exclusive `mut` receivers require unshared writable sources or fresh `new` allocations (`E0510` on unacknowledged shared aliases, `E0520` on immutable/`ref` sources, `E0406` on `^mut` marker).
  - Shared `^mut` receivers require writable sources and explicit `^mut` acknowledgment on existing roots (`E0510`).
  - Persistent `let ref` / `var ref` receivers require pinned `let mut` origins, existing `ref` handles, or immutable shared objects (`E0531` on reassignable `var` roots, `E0543` on unanchored fresh allocations or borrowed sum-subset re-wraps).
  - `new` receivers require fresh construction results or explicit `new x` handoff ending `x` (`E0548`, `E0549`).

### Bidirectional Expression Checking

- **Synthesis & Checking (`K-EXPR`)**: Operands evaluate and check left-to-right; contextual expected types propagate inward to empty array/map literals (`[]`), anonymous closures (`\x -> ...`), sum constructors (`Ok 1` under `Result<int, str>`), and `if`/`match` arms (`E0344` if any type parameter or anonymous closure parameter type remains undetermined).
- **Monomorphic Anonymous Closures**: Anonymous functions `\x -> ...` resolve concrete parameter and return types from call-site/binding context or explicit parameter annotations (`\x: int -> x + 1`); unannotated standalone polymorphic lambdas without determining context fail `E0344`.

### Structural Joins and Normal Continuations

- **K-JOIN**: Branches with no normal continuation (`never` from `return`, `break`, `continue`, `panic`, `?`) contribute their prior side effects and obligations without constraining the join result type. Normally completing branches must join to a common type (`E0351` on incompatible types).
- **K-TYPE-RESULT**: In `TypeFunctionExpr` bodies, different static branches may return `Type<A>` and `Type<B>` tokens for distinct well-formed types `A` and `B`; closed evaluation yields the selected branch's single rigid token.

### Generic Evidence and Definition Checking

- **K-GEN**: Generic function bodies typecheck once at definition time against all admitted instantiations (`E0301` on unproved operations).
- **K-GEN-MATCH**: Transparent unguarded type-pattern decision trees (`\T -> match <T> { <int> | <f64> -> <T>, _ -> <never> }`) supply path-specific positive/negative type evidence to constrained generic bodies.

### Authority, Calls, and Contract Operations

- **K-CALL**: Call preparation evaluates arguments left-to-right, freezes the call-entry reachability graph, immediately ends any `new arg` source path (`E0549` on later arguments reading `arg`), checks cross-argument aliasing exclusivity (`E0523`, `E0524`), and instantiates return origins (`ref(x)`, `^mut(x)`, `&return{...}`).
- **Pure Constant Origins**: Reading module-level pure immutable constants (`let` or ordinary-valued `meta let`) introduces **zero** `&up` state or capture obligations.

### Recursive Summaries and Grounded Inference

- **K-FIX**: Mutually recursive functions and `via` mode families compute grounded fixed-point summaries over actual writes, captures, escapes, and unhandled operational effects. Freshness (`new`), isolation, and local state discharge require grounded non-circular proofs.

### Phase Checking and Static Evaluation

- **K-PHASE**:
  - `TypeEval` and `MetaValue` run under the compiler's root step budget (`E0811` on exhaustion; `E0830` on failed `assert`; `E0831` on `panic` or run-time arithmetic defect).
  - Run-time parameters, results, storage, and captures cannot materialize `Type<T>` tokens (`E0816`). `meta fn` return types cannot expose `Type<T>` tokens (`E0812`) or effect/state annotations (`E0813`).
  - Direct saturated calls to `meta fn` with compile-time constant arguments (`E0814` on runtime arguments) are permitted in `RunTime` value expressions: the compiler evaluates the call at compile time under `E0811`/`E0831`, rejects tokens (`E0812`) and callables/resources (`E0816`), strips `new` construction qualification, and publishes the result as a deeply immutable snapshot (`E0520` if bound directly to `let mut`; use `clone(f(...))` for a fresh mutable copy). Referencing a `meta fn` as a first-class runtime function value fails `E0810`.
  - `typeof expr` typechecks `expr` in an isolated static context (enforcing internal `E0549` sequencing) and yields its static type without evaluating `expr` or emitting outward effects/writes.

```ril
meta fn build_lookup(scale: int) -> []int {
    [1 * scale, 2 * scale, 3 * scale]
}

fn sample(i: int) -> int {
    let table = build_lookup(10)       -- OK: compile-time folded immutable []int snapshot
    -- let mut bad = build_lookup(10)  -- Error [E0520]: 'meta fn' fold strips 'new' freshness
    -- let fn_ref = build_lookup       -- Error [E0810]: 'meta fn' is not a runtime function value
    table[i]
}
assert(sample(1) == 20)
```

### Semantic Interfaces and Diagnostic Boundaries

- **K-IFACE**: Compiled module interfaces retain normalized parameter/return schemas, `via` mode correlations, `close` cleanup contracts, `Sendable` / `SharedObject` representation facts across `opaque` boundaries, operational-effect footprints, and provenance relations.

---

## Declarations and Bindings

```ebnf
LetDecl               ::= [ Visibility ] "let" Pattern [ ":" TypeExpression ] "=" Expression
LetMutDecl            ::= "let" "mut" Pattern [ ":" TypeExpression ] "=" Expression
SharedMutDecl         ::= ( "let" | "var" ) "^mut" ( ValueName | "_" ) [ ":" TypeExpression ] "=" Expression
VarDecl               ::= "var" ( ValueName | "_" ) [ ":" TypeExpression ] "=" Expression
VarMutDecl            ::= "var" "mut" ( ValueName | "_" ) [ ":" TypeExpression ] "=" Expression
LetRefDecl            ::= "let" "ref" Pattern [ ":" TypeExpression ] "=" Expression
VarRefDecl            ::= "var" "ref" ( ValueName | "_" ) [ ":" TypeExpression ] "=" Expression
ModePreservingBinding ::= "let" "via" Pattern [ ":" TypeExpression ] "=" Expression
ScopedDecl            ::= "let" "scoped" [ "mut" ] ( ValueName | "_" ) [ ":" TypeExpression ] "=" Expression
```

### Binding Modes and Storage Matrix

| Form | Slot rebinding | Interior access | Required source |
| :--- | :---: | :--- | :--- |
| `let x = e` | Fixed (`E0501`) | Deeply immutable (`E0520`) | Snapshot free of live writers/refs (`E0535`) |
| `var x = e` | Reassignable | Deeply immutable (`E0520`) | Snapshot free of live writers/refs (`E0535`) |
| `let mut x = e` | Pinned (`E0502`) | Exclusive writable | Fresh `new` / constructor or unaliased handoff |
| `var mut x = e` | Reassignable | Exclusive writable | Fresh `new` / constructor (cannot anchor `let ref`, `E0531`) |
| `let ^mut x = e` | Pinned (`E0502`) | Shared writable | Writable handle (`^mut` marker on existing shared source) |
| `var ^mut x = e` | Reassignable | Shared writable | Writable handle (`^mut` marker on replacement) |
| `let ref x = e` | Pinned (`E0502`) | Read-only live view (`E0520`) | Pinned `let mut`, `ref`, or immutable shared object (`E0531`, `E0543`) |
| `var ref x = e` | Reassignable | Read-only live view (`E0520`) | Eligible `ref` origin on each assignment (`E0531`, `E0543`) |

#### Sound Upper-Bound Authority

<a id="reachable-authority-use"></a>

Declared slot mutability (`var`), interior mutability (`mut`, `^mut`), parameter modes, and function state annotations (`&mut`, `&^mut`, `&capture`, `&up{...}`) act as **verified upper bounds**:
- Performing an operation exceeding declared authority is rejected (`E0501`, `E0502`, `E0510`, `E0520`, `E0528`).
- Declaring broader authority than a body or callback happens to exercise (such as a no-op callback `\mut _: Cell -> ()` matching `fn(mut Cell) &mut -> ()`, or an unused `mut` parameter) is **valid**.

```ril
type Cell = .{ var count: int }

fn run_hook(mut c: Cell, hook: fn(mut Cell) &mut -> ()) &mut -> () {
    hook(mut c)
}

let mut c = Cell.{ count: 5 }
run_hook(mut c) \mut _unused -> ()     -- OK: no-op callback satisfies upper-bound contract
assert(c.count == 5)
```

### Construction-Qualified Locals and Mode-Preserving Reception

A pinned `let mut` local initialized from a constructor, `clone(...)`, `-> new T` call, or `new src` handoff retains static `new` construction qualification as long as no `^mut` alias or escaping reference is formed. Passing `new x` transfers ownership in-place and immediately ends `x` and any derived views (`E0549`).

```ril
type Buffer = .{ mut items: []int }

fn build_buffer() -> new Buffer {
    let mut b = Buffer.{ items: [] }
    Array::push(mut b.items, 1)
    b                                  -- OK: 'b' retains 'new' qualification; local write discharges
}

let mut b1 = build_buffer()
let mut b2 = new b1                    -- Handoff ends 'b1'
-- let n = len(ref b1.items)           -- Error [E0549]: 'b1' ended at handoff
assert(len(ref b2.items) == 1)
```

### Immutable, Mutable, Shared, and Reference Bindings

```ril
type Doc = .{ var title: str }
let fixed_doc = Doc.{ title: "v0" }
-- fixed_doc = Doc.{ title: "v1" }     -- Error [E0501]: plain 'let' slot cannot be reassigned
let mut draft = Doc.{ title: "v1" }
-- let mut bad_unack = draft           -- Error [E0510]: shared alias requires '^mut' acknowledgment
let ^mut shared = draft                -- Explicit shared writable handle
let ref reader = draft                 -- Pinned read-only live observer

shared.title = "v2"
assert(reader.title == "v2")
-- reader.title = "v3"                 -- Error [E0520]: 'ref' grants no write authority
-- draft = Doc.{ title: "new" }        -- Error [E0502]: 'let mut' handle is pinned
-- let ref bad_fresh = Doc.{ title: "x" } -- Error [E0543]: unanchored fresh allocation cannot bind 'let ref'

var slot = Doc.{ title: "snap1" }
slot = Doc.{ title: "snap2" }          -- OK: slot replacement of immutable snapshots
-- let ref bad_obs = slot              -- Error [E0531]: reassignable 'var' cannot anchor 'let ref'
```

### Scoped Resource Bindings

`let scoped [mut] x = expr` binds a non-escaping resource whose static type `T` declares an accessible `close <fn_name>` cleanup contract (`E0541` otherwise).

```ril
pub opaque type DbConn = .{ var open: bool, mut log: []str } close release_conn

pub fn release_conn(mut c: DbConn) @Io &mut -> () {
    c.open = false
    println("closed")
}

pub fn acquire(mut log: []str) -> new DbConn {
    DbConn.{ open: true, log: clone(ref log) }
}

fn run_query() @Io -> Result<int, str> {
    let mut init_log: []str = []
    let scoped mut conn = acquire(mut init_log)
    -- let scoped bad_ro = acquire(mut init_log) -- Error [E0541]: 'release_conn' requires 'mut' binding
    -- let scoped bad_plain = 42                 -- Error [E0541]: 'int' declares no 'close' contract
    -- var scoped bad = acquire(mut init_log)    -- Error [E0532]: scoped bindings cannot be 'var'
    -- return conn                               -- Error [E0604]: scoped binding cannot escape block
    Ok 1                                         -- Invokes release_conn(mut conn) before returning
}
-- fn missing_io() -> () { let mut l: []str = []; let scoped mut _c = acquire(mut l) } -- Error [E0612]: unhandled @Io from release_conn
```

| `let scoped` & `close` rule | Requirement |
| :--- | :--- |
| Eligible declarations (`E0541`) | `close fn_name` is permitted on `OpaqueTypeDecl`, payload-bearing `NominalDecl`, `SumTypeDecl`, and `.d.ril` `DeclResourceType` (never on transparent `type A = B`). `fn_name` must resolve in the same scope to a function returning `()` with 1 parameter matching `Self` (including generic parameters) |
| Parameter mode & binding match (`E0541`) | `fn(mut Self) [@Eff] &mut -> ()` requires `let scoped mut x`; `fn(Self) [@Eff] -> ()` or `fn(ref Self) [@Eff] -> ()` admits `let scoped x` (`ref Self` also admits `let scoped mut x`). `close` functions must not declare `&^mut` or `&capture` (`E0541`), and must satisfy `E0910` visibility relative to the type |
| Static effect propagation (`E0612`) | Operational effects `@Eff` on `close_fn` (such as `@Io`) are charged to the `let scoped` site and must be handled or declared by the enclosing callable (`E0612`) |
| Confinement & non-reassignment (`E0532`, `E0604`) | `scoped` forbids `var` (`E0532`), forbids `^mut` sharing, and forbids `new x` handoff, return escape, or closure capture of `x` or references derived from `x` (`E0604`) |
| Deterministic LIFO & Double-Fault | Runs once per initialized binding in reverse declaration order on normal block exit, `return`, `break`, `continue`, `?`, panic unwinding, and unshielded `@Async` cancellation. If `close_fn` panics while another panic or cancellation is already unwinding, the process terminates immediately (bypassing `absorb_panic`) |

### Declaration Metadata Attributes

Compile-time `meta(expr1, expr2)` attributes attach deeply immutable constant values (`E0814` on non-static expressions, `E0812`/`E0816` on tokens/callables) to nominal, opaque, sum, record-field, variant, effect, or function declarations (`E0708` on transparent `type A = B` aliases, `use`, or local `let`/`var` statements).

```ebnf
MetaAttr    ::= "meta" "(" MetaArgList ")"
MetaArgList ::= Expression { "," Expression } [ "," ]
```

```ril
pub type Route str
pub type Role str

meta(Route "/users", Role "admin")
pub type CreateUserReq .{
    meta(Role "pii")
    email: str,
}
-- meta(Route "/x") type BadAlias = int -- Error [E0708]: 'meta(...)' prohibited on transparent alias
```

### External Interface Declarations

External host contracts reside in `.d.ril` files (`DeclUnitItem`). `.d.ril` files contain declarations without bodies (`E0901` on bodies or `opaque`; standard `.ril` functions without bodies fail `E0902` unless matching a registered language built-in).

```ebnf
DeclUnitItem     ::= UseDecl | DeclFunction | DeclType | DeclEffect | DeclLet
DeclFunction     ::= { MetaAttr } [ Visibility ] "fn" ValueName [ GenericParams ]
                     "(" [ ParameterList ] ")" ReturnSpec
DeclType         ::= DeclSumType | DeclNominalType | DeclTypeAlias | DeclResourceType
DeclSumType      ::= { MetaAttr } [ Visibility ] "type" PascalCase [ GenericParams ]
                     "{" VariantDeclList "}" [ CloseClause ]
DeclNominalType  ::= { MetaAttr } [ Visibility ] "type" PascalCase [ GenericParams ]
                     [ TypeExpression ] [ CloseClause ]
DeclTypeAlias    ::= [ Visibility ] "type" PascalCase [ GenericParams ] "=" TypeExpression
DeclResourceType ::= { MetaAttr } [ Visibility ] "resource" "type" PascalCase [ GenericParams ]
                     [ CloseClause ]
DeclEffect       ::= { MetaAttr } [ Visibility ] "eff" PascalCase [ GenericParams ]
                     "{" [ EffectMemberList ] "}"
DeclLet          ::= [ Visibility ] "let" ValueName ":" TypeExpression
```

| `.d.ril` contract rule | Requirement |
| :--- | :--- |
| Field & representation sealing (`E0907`) | Foreign nominal types have host-managed representations; `.ril` code cannot penetrate unexported host fields (`E0907`) |
| Supported authority (`E0908`) | Foreign signatures cannot use `^mut`, `&^mut`, `&capture`, or `via`/`infer` (`E0908`); exclusive `new`, `mut`, and `ref` contracts are supported |
| `resource type` handles | `pub resource type OwnedFd close close_fd` models exclusive host handles without mandatory-consumption viral errors: forbids `clone`, `derive`, `==`, plain `let` freezing, `^mut`, and `[M]OwnedFd` arrays (`E0301`, `E0411`); supports `new` creation/consumption (`E0549` after `new fd`), `let mut`, `mut`, `ref`, and `let scoped mut` |
| Pure `DeclLet` & `@Io` isolation (`E0906`, `E0608`) | `DeclLet` admits pure immutable value/data constants only (`resource` or mutable handles in `DeclLet` fail `E0906`); host-stateful foreign functions must declare `@Io` so `absorb_panic` (`E0608`) modularly isolates host side effects |

```ril
-- File: sys/posix.d.ril
pub resource type OwnedFd close close_fd

pub fn open_path(path: str) @Io -> new Result<OwnedFd, str>
pub fn read_bytes(ref fd: OwnedFd, max_len: int) @Io -> Result<bytes, str>
pub fn close_fd(mut fd: OwnedFd) @Io &mut -> ()
-- pub fn bad_body() -> int { 1 }          -- Error [E0901]: bodies prohibited in .d.ril
-- pub fn bad_shared(^mut fd: OwnedFd) -> () -- Error [E0908]: '^mut' unsupported on foreign contracts
-- In .ril file:
-- fn unimplemented() -> int               -- Error [E0902]: body required in standard .ril module
-- let _ = fd.internal_handle              -- Error [E0907]: foreign representation is sealed
```

---

## Expressions and Operators

### Expression Grammar and Precedence

```ebnf
Expression               ::= AssignmentExpr | AnonFnExpr
AssignmentExpr           ::= AssignTarget AssignmentOperator Expression
                           | SubsetWidenExpr
AssignTarget             ::= ValueName | MemberExpr | IndexExpr
AssignmentOperator       ::= "=" | "+=" | "-=" | "*=" | "/=" | "%="
                           | "&=" | "|=" | "^=" | "<<=" | ">>="
SubsetWidenExpr          ::= FallbackExpr [ "as" TypeReference ]
FallbackExpr             ::= PipelineExpr { "??" PipelineExpr }
PipelineExpr             ::= BinaryExpr { "|>" BinaryExpr }
BinaryExpr               ::= RangeExpr { BinaryOperator RangeExpr }
BinaryOperator           ::= "||" | "&&"
                           | "==" | "!=" | "<" | "<=" | ">" | ">="
                           | "|" | "^" | "&"
                           | "<<" | ">>"
                           | "+" | "-" | "*" | "/" | "%"
RangeExpr                ::= UnaryExpr [ ( ".." | "..=" ) UnaryExpr ]
SliceRangeExpr           ::= [ UnaryExpr ] ( ".." | "..=" ) [ UnaryExpr ]
UnaryExpr                ::= ( "-" | "!" | "~" ) UnaryExpr
                           | ConstructionTransferExpr
                           | SharingExpr
                           | ConstructorExpr
                           | PostfixExpr
ConstructionTransferExpr ::= "new" PostfixExpr
SharingExpr              ::= "^mut" PostfixExpr
ConstructorExpr          ::= ConstructorPath [ "new" | "^mut" ] ConstructorArg
ConstructorPath          ::= { PascalCase "::" } PascalCase [ GenericArgs ]
ConstructorArg           ::= ( "!" | "~" ) ConstructorArg
                           | PostfixAtomExpr
PostfixExpr              ::= CallExpr | MemberExpr | IndexExpr
                           | PostfixExpr "?"
                           | AtomExpr
                           | Block
CallExpr                 ::= PostfixExpr "(" [ ArgumentList ] ")" [ TrailingClosure ]
                           | PostfixExpr TrailingClosure
TrailingClosure          ::= AnonFnExpr
ArgumentList             ::= Argument { "," Argument } [ "," ]
Argument                 ::= [ ArgumentMode ] Expression
ArgumentMode             ::= "mut" | "ref" | "^mut" | "new"
MemberExpr               ::= PostfixExpr ( "." | "?." ) ( FieldLabel | Digit+ | "(" Expression ")" )
IndexExpr                ::= PostfixExpr [ "?" ] "[" ( Expression | SliceRangeExpr ) "]"
PostfixAtomExpr          ::= AtomExpr
                           | PostfixAtomExpr "(" [ ArgumentList ] ")"
                           | PostfixAtomExpr ( "." | "?." ) ( FieldLabel | Digit+ | "(" Expression ")" )
                           | PostfixAtomExpr [ "?" ] "[" ( Expression | SliceRangeExpr ) "]"
                           | PostfixAtomExpr "?"
AtomExpr                 ::= Literal
                           | QualifiedName [ GenericArgs ]
                           | RecordExpr
                           | TupleExpr
                           | ArrayExpr
                           | MapExpr
                           | TypeQuoteExpr
                           | IfExpr | MatchExpr | LoopExpr | WhileExpr | ForExpr
                           | "(" Expression ")"
TypeQuoteExpr            ::= "<" TypeExpression ">"
RecordExpr               ::= [ TypeReference ] ".{" [ RecordValueField { "," RecordValueField } [ "," ] ] "}"
RecordValueField         ::= FieldLabel [ ":" Expression ]
TupleExpr                ::= "(" Expression "," Expression { "," Expression } [ "," ] ")"
ArrayExpr                ::= "[" [ Expression { "," Expression } [ "," ] ] "]"
MapExpr                  ::= "[" ":" "]"
                           | "[" MapEntry { "," MapEntry } [ "," ] "]"
MapEntry                 ::= Expression ":" Expression
```

| Precedence (high → low) | Operators / forms | Associativity |
| :---: | :--- | :---: |
| 1 | `.` `?.` `f(...)` `f \...` `a[i]` `a?[i]` `?` `Type.{...}` | Left |
| 2 | Unary `-` `!` `~`, `new e`, `^mut e`, space constructor `Tag arg` | Right |
| 3 | `*` `/` `%` | Left |
| 4 | `+` `-` | Left |
| 5 | `<<` `>>` | Left |
| 6 | `&` | Left |
| 7 | `^` | Left |
| 8 | `\|` | Left |
| 9 | `..` `..=` | Non-associative |
| 10 | `==` `!=` `<` `<=` `>` `>=` | Non-associative |
| 11 | `&&` | Left (short-circuit) |
| 12 | `\|\|` | Left (short-circuit) |
| 13 | `\|>` | Left |
| 14 | `??` | Left (short-circuit) |
| 15 | `e as SupType` | Left |
| 16 | `=` `+=` `-=` `*=` `/=` `%=` `&=` `\|=` `^=` `<<=` `>>=` | Non-associative (`E0701`) |

- **Lexical Adjacency vs. Space Construction (`E0125`)**: Function calls attach `(` (`parse(s)`), array/map indexing attaches `[` (`xs[0]`), and all named record constructions attach `.{` (`User.{ id: 1 }`). Sum variants and non-record nominal constructors require whitespace before their payload (`Ok 42`, `Ok ()`, `Some .{ x: 1 }`, `Some [1, 2]`, `Ok (-1)`). Bare `Block` `{...}` and bare `AnonFnExpr` `\...` are excluded from `ConstructorArg`, so `if opt == None { ... }` and `call(None) \-> ...` parse unambiguously.

### Arithmetic, Bitwise, Relational, and Logical Operators

- **Arithmetic (`+`, `-`, `*`, `/`, `%`, unary `-`)**: Defined on `(int, int) -> int` and `(f64, f64) -> f64` (`+` also concatenates `(str, str) -> str` and `(bytes, bytes) -> bytes`). Integer `/` truncates toward zero and `%` satisfies `(a / b) * b + (a % b) == a`. Constant integer division/remainder by `0` fails `E0361`; dynamic `/ 0` or `% 0` panics. Explicit numeric conversions use `Numeric::to_f64(n: int) -> f64` and `Numeric::to_int(x: f64) -> ?int` (`None` on NaN/$\pm\infty$).
- **Bitwise & Shifts (`~`, `&`, `|`, `^`, `<<`, `>>`)**: Defined exclusively on `int` (`E0327` on `f64`, `bool`, etc.) using infinite-width two's-complement semantics (`~x == -x - 1`, `x >> k` arithmetic floor shift). Constant negative shift count `k < 0` fails `E0361`; dynamic `k < 0` panics.
- **Equality & Ordering (`==`, `!=`, `<`, `<=`, `>`, `>=`)**:
  - `==` / `!=` require same-type operands (`E0301`) whose type recursively excludes callables, `resource` handles, `Task`, `Sender`, `Receiver`, and `Draft` (`E0327`; `f64` follows IEEE-754 where `NaN != NaN` and `-0.0 == 0.0`). Map keys and `Set` elements additionally forbid `f64` and mutable member modes (`E0328`).
  - `<`, `<=`, `>`, `>=` apply to `int`, `f64`, `str` (lexicographic UTF-8 scalar order), and `bytes` (`E0327` elsewhere).
- **Logical (`!`, `&&`, `||`)**: Require `bool` operands (`E0350`); `&&` and `||` short-circuit left-to-right.

```ril
assert(7 / 3 == 2 && -7 / 3 == -2 && -7 % 3 == -1)
assert((~0 == -1) && ((-8 >> 2) == -2) && ((1 << 100) > 0))
-- let bad_div = 10 / 0                -- Error [E0361]: constant zero divisor
-- let bad_shl = 1 << -3               -- Error [E0361]: constant negative shift count
-- let bad_bit = true & false          -- Error [E0327]: bitwise '&' requires 'int'
```

### Indexing, Slicing, and Static Coordinate Projection

- **Indexing & Slicing (`xs[i]`, `xs[a..b]`, `xs[a..=b]`)**:
  - Arrays `[M]T` and `bytes` accept `int` indices (`E0352` on non-indexable receivers like `str` or records; `str` indexing uses `String::scalars` / `String::slice_bytes`; record bracket indexing fails `E0324`). Out-of-bounds indices/slices panic at run time.
  - Maps `[K: M V]` return `V` on `m[k]` (panicking if absent) and `?V` on safe `m?[k]` (`None` if absent; for `[K: mut V]` / `[K: ref V]`, safe indexing observes without panicking). Mutating a live array/map while holding a `ref` element projection or during `for` iteration over it fails `E0537` / `E0526`.
- **Tuple & Static Coordinate Projection (`t.0`, `r.(key)`)**: `t.0` projects tuple elements (`E0312` out of bounds; `E0337` on sums/primitives); `r.(key)` projects a record field or tuple slot using a compile-time `meta` coordinate `key` validated by `Key<T>`.

```ril
let xs = [10, 20, 30, 40]
assert(xs[1..3] == [20, 30] && xs[..=1] == [10, 20])
let m = ["port": 8080]
assert(m?["port"] == Some 8080 && m?["host"] == None)
-- let _ = "abc"[0]                    -- Error [E0352]: 'str' is not directly bracket-indexable
-- let _ = (Some 1).0                  -- Error [E0337]: tuple projection on sum type
type Cell = .{ var v: int }
let mut cells = [Cell.{ v: 1 }]
let ref elem = cells[0]
-- Array::push(mut cells, Cell.{ v: 2 }) -- Error [E0537]: mutating array while 'ref' element view is live
assert(elem.v == 1)
```

### Text and Byte Operations

String concatenation uses `+` or interpolation `"{a}{b}"`; byte concatenation uses `+`. Safe array-to-bytes conversion uses `Bytes::from_array(via values: []int) -> ?bytes`, returning `None` if any element lies outside `0..=255`.

```ril
assert(Bytes::from_array([65, 66]) == Some bytes"AB")
assert(Bytes::from_array([256]) == None)
assert(Bytes::from_array([-1]) == None)
```

### Pipeline and Fallible Operators

- **Value Pipeline (`x |> f(a, b)` / `x |> f` / `x |> Ok`)**: Evaluates `x` first, then passes `x` as the first plain value argument to `f` (`f(x, a, b)` or `f(x)`). Non-callable targets fail `E0338`. In-place mutation uses prefix calls (`Array::push(mut xs, v)`), never mode-carrying pipelines.
- **Error/Option Propagation (`expr?`)**: Valid inside an ordinary function or closure body (`E0205` at module top-level):
  - On `Result<T, E>` (`E0712` on non-`Result`/non-`Option`): unwraps `Ok v` to `v`, or early-returns `Err e` (widening `e` when $E \preceq_{\text{sum}} E_{\text{ret}}$; incompatible enclosing return types fail `E0713`).
  - On `?T`: unwraps `Some v` to `v`, or early-returns `None` when the enclosing callable returns `?U` (`E0713` otherwise).
- **Fallback (`opt ?? default` / `res ?? \err -> fallback`)**:
  - `?T ?? T`: evaluates right operand lazily only on `None` (`E0714` on invalid left operand).
  - `Result<T, E> ?? fn(E) @... -> T`: invokes the handler closure with `e` on `Err e`, discharging `Result`'s `E0720` obligation (`E0711` if right operand is not `fn(E) -> T`; outer `break`/`continue`/`return` across a closure boundary fails `E0707`/`E0710`).
- **Safe Navigation (`opt?.field`, `opt?[idx]`)**: Requires `?T` receiver (`E0715` otherwise); short-circuits `None` to `None` and wraps present projections in `?U` (flattening `? ?U` to `?U` when `field` itself is optional).

```ril
type Config = .{ host: ?str }
fn resolve_host(cfg: ?Config) -> str {
    cfg?.host ?? "localhost"
}
assert(resolve_host(Some Config.{ host: Some "ril.dev" }) == "ril.dev")
assert(resolve_host(None) == "localhost")
-- let top_q = (Ok 1)?                 -- Error [E0205]: '?' outside function/closure frame
-- let _ = 1 |> 2                      -- Error [E0338]: pipeline target is not callable
-- let _ = 42?                         -- Error [E0712]: '?' requires Result or Option
-- fn bad_prop() -> int { (None)? }    -- Error [E0713]: enclosing return type is not Option
-- let _ = 42 ?? 0                     -- Error [E0714]: '??' requires Option or Result
-- let _ = (Ok 1) ?? 0                 -- Error [E0711]: Result '??' requires error handler 'fn(E) -> T'
-- let _ = 42?.host                    -- Error [E0715]: '?.' requires optional '?T' receiver
-- for [1] as _ { let _ = (Err "e") ?? \_ -> break } -- Error [E0710]: loop transfer across fallback closure
```

### Record Construction and Assignments

- **Record Construction (`[Type].{ field: expr, shorthand }`)**: Must initialize every declared field of the target record type (`E0307` missing, `E0302` unexpected, `E0210` duplicate). Field punning `.{ id, name }` desugars to `.{ id: id, name: name }`.
- **Assignments (`target = expr`, `target += expr`, ...)**: Assignment is a `()`-typed expression and does not chain (`a = b = 1` fails `E0701`). `target` must be a `var` variable, a `var` record field on a `mut`/`^mut` path, or an element of a `mut`/`^mut` array/map (`E0501` on `let`, `E0502` on pinned `let mut`/`let ref`, `E0503` on rvalues). Compound assignments evaluate `target`'s receiver/index expression exactly once.

```ril
var a = 1
var b = 2
a += b
-- 10 = 20                             -- Error [E0503]: invalid assignment target
-- a = b = 3                           -- Error [E0701]: chained assignment is prohibited
```

---

## Control Flow and Pattern Matching

### Block Expressions and Local Declarations

<a id="dual-tier-where-invariants"></a>

```ebnf
Block             ::= "{" [ StatementSequence ] "}"
StatementSequence ::= Statement { Separator Statement } [ Separator ]
Statement         ::= UseDecl
                    | LocalTypeDecl
                    | FunctionDecl
                    | EffectDecl
                    | MetaFnDecl
                    | MetaLetDecl
                    | LetDecl | LetMutDecl | SharedMutDecl
                    | VarDecl | VarMutDecl | LetRefDecl | VarRefDecl
                    | ModePreservingBinding | ScopedDecl
                    | GuardedLetStmt
                    | WithStatement
                    | ControlTransfer
                    | Expression
Separator         ::= ";" | Newline
```

- **Value of a Block**: A block evaluates statements top-to-bottom; its value is the trailing `Expression` if not followed by `;`, or `()` otherwise.
- **Sequential Scope & Mutual Recursion (`E0207`, `E0315`, `E0618`)**:
  - Value bindings (`let`, `var`, `let scoped`) enter scope strictly after their initializer completes (`E0207` on self/forward reference before initialization).
  - Contiguous runs of local `type`, `fn`, `meta fn`, and `eff` declarations form a mutually recursive group visible throughout the remainder of the block. Local `fn`s may capture only value bindings initialized **before** that contiguous declaration group (`E0207`).
  - Block-local nominal/opaque/sum types cannot escape in the enclosing callable's return type or outer mutable storage (`E0315`). Block-local `eff` effects must be handled inside their declaring block (`E0618`). Visibility modifiers (`pub`, `pub(pkg)`) are forbidden inside blocks (`E0120`).

```ril
fn compute_tree() -> int {
    -- let bad_self = bad_self + 1     -- Error [E0207]: 'bad_self' used before initialization
    let base = 10
    type Tree { Leaf int, Node (Tree, Tree) }
    fn sum(t: Tree) -> int {
        match t {
            Leaf v      -> v + base,
            Node (l, r) -> sum(l) + sum(r),
        }
    }
    -- eff LocalEff { fn ping() -> () }; LocalEff::ping() -- Error [E0618]: local effect escapes block unhandled
    sum(Node (Leaf 1, Leaf 2))         -- Returning 'Leaf 1' from 'compute_tree' would fail E0315
}
assert(compute_tree() == 23)
```

### Conditional and Loop Expressions

```ebnf
IfExpr          ::= "if" ( Expression | "let" Pattern "=" Expression ) Block
                    [ "else" ( IfExpr | Block ) ]
LoopExpr        ::= "loop" Block
WhileExpr       ::= "while" ( Expression | "let" Pattern "=" Expression ) Block
ForExpr         ::= "for" Expression "as" Pattern Block
ControlTransfer ::= "return" [ Expression ]
                  | "break"
                  | "continue"
```

- **Conditionals**: `if cond { a } else { b }` requires `cond: bool` (`E0350`) and a common join type across normal branches (`E0351`). Without `else`, the `then` block must have type `()` (or `never`). `if let pat = expr { ... } [else { ... }]` matches refutable `pat` against `expr`.
- **Loops & Transfers (`E0355`, `E0707`)**:
  - `loop { ... }` repeats until `break` or `return` (type `()` if `break` is reachable, `never` otherwise).
  - `while cond { ... }` and `while let pat = expr { ... }` evaluate to `()`.
  - `for iter as pat { ... }` iterates over `[]T`, `[K: V]` (yielding `(K, V)`), `Set<T>`, or integer ranges `a..b` / `a..=b` (`E0355` on non-iterable values), evaluating to `()`. `pat` must be irrefutable (`E0345`).
  - `break` and `continue` target the innermost enclosing loop in the same callable (`E0707` outside a loop or across a closure boundary). `return` exits the innermost enclosing `fn` or `\... ->` closure (`return` ≡ `return ()`).

```ril
var acc = 0
for 1..=10 as i {
    if i % 2 == 0 { continue }
    if i > 7 { break }
    acc += i
}
assert(acc == 16)
-- if 1 { () }                         -- Error [E0350]: condition must be 'bool'
-- let _ = if true { 1 } else { "no" } -- Error [E0351]: incompatible branch types 'int' and 'str'
-- for 42 as x { () }                  -- Error [E0355]: 'int' is not iterable
-- break                               -- Error [E0707]: 'break' outside loop
```

### Guarded Bindings

```ebnf
GuardedLetStmt ::= "let" [ "mut" | "ref" | "^mut" ] Pattern "=" Expression "else" Block
```

`let Pat = expr else { ... }` matches refutable `Pat`; on mismatch, the `else` block executes and **must** diverge (`never` via `return`, `break`, `continue`, `panic`, or `?`; normal completion of `else` fails `E0321`). Guarded `let ... else` is explicitly exempt from `E0309`, permitting zero-binder assertions such as `let Ok () = check() else { return Err "denied" }`.

Plain `let Pat = expr` without `else` requires an irrefutable pattern (`E0345`) that introduces at least one variable binder (except explicit `let _ = expr`; vacuous `let () = f()` fails `E0309`).

```ril
fn validate(header: ?str, check: fn(str) -> Result<(), str>) -> Result<str, str> {
    let Some str["Bearer ", ..token] = header else { return Err "missing bearer" }
    let Ok () = check(token) else { return Err "invalid token" }
    -- let Some x = header             -- Error [E0345]: refutable pattern in plain 'let'
    -- let () = ()                     -- Error [E0309]: vacuous pattern binds zero names
    -- let Some y = header else { () } -- Error [E0321]: 'else' block must diverge ('never')
    Ok token
}
```

### Pattern Matching

<a id="value-tests-with-is"></a>
<a id="flow-sensitive-type-narrowing"></a>

```ebnf
MatchExpr            ::= "match" Expression "{" [ MatchArm { "," MatchArm } [ "," ] ] "}"
MatchArm             ::= Pattern [ "if" Expression ] "->" Expression
Pattern              ::= OrPattern
OrPattern            ::= SinglePattern { "|" SinglePattern }
SinglePattern        ::= SubsetPattern
                       | ConstructorPattern
                       | PatternAtom
                       | RangePattern
                       | TypePattern
                       | BindingModifier ValueName
SubsetPattern        ::= TypeReference "as" ( [ BindingModifier ] ValueName | "_" )
ConstructorPattern   ::= ConstructorPath PatternAtom
PatternAtom          ::= LiteralPattern
                       | WildcardPattern
                       | ValueName
                       | ConstructorPath
                       | "(" [ PatternList ] ")"
                       | ArrayPattern
                       | StrPattern
                       | RecordPattern
PatternList          ::= Pattern { "," Pattern } [ "," ]
BindingModifier      ::= "var" [ "mut" | "^mut" | "ref" ]
                       | "mut" | "^mut" | "ref"
ArrayPattern         ::= "[" [ ArrayPatternElement { "," ArrayPatternElement } [ "," ] ] "]"
ArrayPatternElement  ::= ".." [ ValueName ] | Pattern
StrPattern           ::= "str[" StrPatternElement { "," StrPatternElement } [ "," ] "]"
StrPatternElement    ::= StringLiteral | RawStringLiteral | ".." [ ValueName ]
RecordPattern        ::= [ TypeReference ] ".{" [ RecordPatternField { "," RecordPatternField } [ "," ] ] "}"
RecordPatternField   ::= ".."
                       | [ BindingModifier ] FieldLabel [ ":" Pattern ]
LiteralPattern       ::= [ "-" ] NumericPattern | StringLiteral | RawStringLiteral
                       | ByteStringLiteral | RawByteLiteral | "true" | "false"
NumericPattern       ::= IntLiteral | FloatLiteral
WildcardPattern      ::= "_"
RangePattern         ::= [ "-" ] IntLiteral ( ".." | "..=" ) [ "-" ] IntLiteral
```

| Pattern rule | Requirement |
| :--- | :--- |
| Symmetry with construction | Tight `Type.{ a, b }` unpacks named records; space-separated `Some x`, `Ok ()`, `Pair (a, b)`, `UserId id` unpack variants and non-record nominals (`E0314` on tuple arity mismatch; `E0349` on arbitrary expressions in patterns) |
| Or-patterns & unique binders (`E0346`, `E0347`) | Alternatives `P1 \| P2` must bind the exact same set of names with identical types and modes (`E0346`); duplicate binder names in one conjunction fail `E0347` |
| Range patterns (`E0348`) | `lo..hi` / `lo..=hi` require non-empty integer intervals (`lo < hi` for `..`, `lo <= hi` for `..=`, `E0348`) |
| `str[...]` non-overlapping slices (`E0349`) | At most one `..` / `..rest` segment (`E0349` on multiple `..` or empty literal segments); matches `s` iff `s` starts with concatenated prefix literals, ends with concatenated suffix literals, and `len(s) >= len(prefix) + len(suffix)` |
| Exhaustiveness & reachability (`E0303`, `E0304`) | `match` must cover all possible inhabitants (`E0303`; `if guard` arms do not count toward coverage). Unreachable arms (including shadowed subset/variant arms) fail `E0304` |
| Pattern reception (`E0521`, `E0551`) | Binder modes (`mut`, `^mut`, `ref`) cannot exceed the subject's authority and declared member modes (`E0521`, `E0551`) |

```ril
fn classify_packet(raw: str) -> str {
    match raw {
        str["{", ..body, "}"] -> "json:{body}", -- Requires len(raw) >= 2; "{" does NOT match!
        str["GET ", ..path]   -> "get:{path}",
        _                     -> "other",
        -- "dead"             -> "never",       -- Error [E0304]: unreachable match arm
    }
    -- match true { true -> 1 }                 -- Error [E0303]: non-exhaustive match (missing 'false')
    -- match (1, 2) { (x, 2) | (1, y) -> 0, _ -> 1 } -- Error [E0346]: or-pattern binder mismatch
    -- let (dup, dup) = (1, 2)                  -- Error [E0347]: duplicate binder 'dup'
    -- match 5 { 10..5 -> 0, _ -> 1 }           -- Error [E0348]: empty range pattern
    -- match raw { str[..a, ..b] -> a, _ -> "" }-- Error [E0349]: multiple '..' in str[...]
}
assert(classify_packet("{ok}") == "json:ok" && classify_packet("{") == "other")
let snap_rec = .{ fixed: [1, 2] }
-- let .{ mut fixed } = snap_rec                -- Error [E0521]: cannot bind 'mut' from immutable record
-- let ref bad_int = 42                         -- Error [E0551]: invalid pattern decomposition mode on 'int'
```

---

## Functions, Closures, and Callables

### Named Function Declarations and Contrast Matrix

```ebnf
FunctionDecl  ::= { MetaAttr } [ Visibility ] "fn" ValueName [ GenericParams ]
                  "(" [ ParameterList ] ")" ReturnSpec [ Block ]
ParameterList ::= Parameter { "," Parameter } [ "," ]
Parameter     ::= RegularParam | MetaParam
RegularParam  ::= [ ParameterMode ] ( ValueName | "_" ) ":" TypeExpression
MetaParam     ::= "meta" ( ValueName | "_" ) [ ":" TypeExpression ] { "|>" PipelineConstraint }
ParameterMode ::= "mut" | "^mut" | "ref" | "new" | "via"
ReturnSpec    ::= [ EffectAnnot ] [ StateAnnot ] "->" ReturnType
ReturnType    ::= [ ReturnMode ] TypeExpression
ReturnMode    ::= "new"
                | "infer"
                | ( "ref" | "^mut" ) "(" ReturnSources ")"
ReturnSources ::= ValueName { "|" ValueName }
```

| Declaration kind | Syntax | Phase | Effects & state |
| :--- | :--- | :--- | :--- |
| Ordinary `fn` | `fn f(...) [@Eff] [&State] -> T { ... }` | Run-time (`len`/`panic`/`assert` dual-phase) | Explicit `@Eff` and `&State` required on named definitions |
| Compile-time `meta fn` | `meta fn f(...) -> T { ... }` | Static (`TypeEval` / `MetaValue` + saturated compile-time fold in `RunTime`) | Pure only (`E0813`); result token-free (`E0812`) |
| Type function | `type F = \T -> <...>` | Static (`TypeEval`) | Pure only (`E0335`); returns single `Type<U>` token |
| Built-in bodyless `fn` | Bodyless `fn` in prelude `.ril` | Per primitive contract | Must match registered primitive module, name, and signature (`E0902`, `E0909`) |
| Foreign `.d.ril` `fn` | Bodyless `pub fn` in `.d.ril` | Run-time | Body prohibited (`E0901`); stateful host calls declare `@Io` |

### Callable Contracts

```ebnf
CallableType        ::= "fn" "(" [ ParameterTypeList ] ")" [ CallableAnnot ] "->" ReturnType
ParameterTypeList   ::= ParameterTypeItem { "," ParameterTypeItem } [ "," ]
ParameterTypeItem   ::= [ ParameterMode ] [ ValueName ":" ] TypeExpression
CallableAnnot       ::= CallableEffectAnnot [ CallableStateAnnot ]
                      | CallableStateAnnot
                      | "@&"
CallableEffectAnnot ::= "@" | "@{}" | EffectAnnot
CallableStateAnnot  ::= "&" | "&{}" | "&up" | StateAnnot
```

#### Mandatory Contract Inference and Completion

The compiler infers complete operational effects and provenance for every callable body:
- Named `fn` declarations must spell all unhandled operational `@Eff` (`E0612`), concrete state obligations (`&mut`, `&^mut`, `&capture`, `&up{...}`, `&return{...}` — `E0510`), and non-plain return modes (`new`, `ref(x)`, `^mut(x)` — `E0544` / `E0528`), except where `via` / `infer` encapsulates mode-dependent obligations.
- Anonymous closures `\... -> ...` infer their exact contract automatically.

#### Closed and Open Callable Rows

|Callable annotation | Operational effects | State & provenance |
| :--- | :--- | :--- |
| *(omitted)* | Closed empty (`@{}`) | Closed pure (`&{}`) |
| `@Io` | Closed `{Io}` | Closed pure (`&{}`) |
| `&up` | Closed empty (`@{}`) | Abstract captured closure environment |
| `@` | Open effect row | Closed pure (`&{}`) |
| `&` | Closed empty (`@{}`) | Open state/provenance row |
| `@&` | Open effect row | Open state/provenance row |

Open markers `@`, `&`, and `@&` are valid only on `CallableType` parameters/fields (`E0547` on named `fn` declarations).

#### Callable Contract Matching

Under `MatchCallable`, a callable value of actual contract $C_{\text{act}}$ satisfies expected `CallableType` $C_{\text{exp}}$ (`E0534` on mismatch, `E0407` on parameter mode mismatch) iff:
1. Parameter count matches (`E0314`), parameter types satisfy contravariance, return type satisfies covariance, and concrete parameter/return access modes match (`E0407`).
2. Every operational effect in $C_{\text{act}}$ appears in $C_{\text{exp}}$ (unless $C_{\text{exp}}$ is effect-open via `@` or `@&`).
3. Every non-pure state/capture obligation in $C_{\text{act}}$ is permitted by $C_{\text{exp}}$ (`&up` admits read-only/pure closure environments; mutable closure environments require caller-side `mut` / `^mut` handle invocation; `&` / `@&` opens state obligations). Pure module constants and pure stateless lexical `fn` handlers reduce to empty state `&{}`.

```ril
-- pub fn len(x: int) -> int            -- Error [E0909]: built-in signature mismatch in prelude
-- fn bad_open() @ -> () {}             -- Error [E0547]: open '@' row prohibited on named 'fn'
-- fn bad_ret(ref a: []int) -> []int { a } -- Error [E0544]: missing 'ref(a)' return mode annotation
-- let pure_cb: fn() -> () = \-> println("hi")         -- Error [E0534]: '@Io' incompatible with pure 'fn() -> ()'
-- let mode_cb: fn([]int) -> () = \mut xs: []int -> () -- Error [E0407]: parameter mode 'mut' vs plain
```

### Return Construction, Access Modes, and Sources

| Return form | Meaning & static check |
| :--- | :--- |
| `-> T` | Deeply immutable snapshot or value copy (`E0528` / `E0535` if live or writable) |
| `-> new T` | Freshly constructed or `new`-transferred graph free of external writable aliases (`E0546`) |
| `-> new [mut]T` | Fresh array holding exclusive writable elements |
| `-> ref(x \| y) T` | Read-only view rooted in formal `x` or `y`'s call-entry graph (`E0545` if rooted in a local or borrowed sum-subset wrapper) |
| `-> ^mut(x) T` | Shared writable handle rooted in `^mut x`'s call-entry graph (`E0545` if `x` is temporary `mut`) |
| `&return{ref x, ^mut y}` | Records contained live/shared origins inside a composite return value |

```ril
type Node = .{ var val: int }

fn pick_ref(cond: bool, ref a: Node, ref b: Node) -> ref(a | b) Node {
    if cond { a } else { b }
}

fn make_mut_nodes() -> new [mut]Node {
    [Node.{ val: 1 }, Node.{ val: 2 }]
}
-- fn bad_src(mut a: Node) -> ^mut(a) Node { a } -- Error [E0545]: temporary 'mut' cannot source '^mut(a)'
-- fn bad_new(ref a: Node) -> new Node { a }     -- Error [E0546] / [E0528]: 'ref' is not fresh 'new'
```

### Parameter Modes and Caller Obligations

<a id="parameter-modes-caller-obligations-and-defaults"></a>

Parameters pass positionally in exact arity (`E0314`); `var` parameters are prohibited (`E0403`; copy into a local `var` if slot replacement is needed). Concrete calls spell explicit argument mode markers (`E0405` if omitted, `E0406` if mismatched, `E0410` if `mut` targets a non-writable expression):

| Formal parameter | Call-site marker | Authority & obligation |
| :--- | :---: | :--- |
| `x: T` | `expr` | Deeply immutable snapshot or value copy (`E0535` on live writer) |
| `ref x: T` | `ref expr` | Scoped read-only borrow of shared object (`E0401` on value type `T`) |
| `mut x: T` | `mut expr` | Temporary exclusive write access for call duration; cannot be retained (`&mut` if mutated) |
| `^mut x: T` | `^mut expr` | Shared writable handle; permits retention in structures/closures (`&^mut` if retained beyond root return) |
| `new x: T` | `new expr` (or fresh rvalue) | Transfers construction/resource ownership (`E0548` on borrowed/shared input; ends `expr` with `E0549`; `E0411` on plain value types) |
| `via x: T` | Mode-dependent | Instantiates static mode template from caller's supplied mode |

```ril
fn bump_node(mut n: Node) &mut -> () { n.val += 1 }
fn consume_node(new n: Node) -> int { n.val }

let mut n0 = Node.{ val: 5 }
bump_node(mut n0)
-- bump_node(n0)                        -- Error [E0405]: missing 'mut' marker at call site
-- bump_node(ref n0)                    -- Error [E0406]: argument mode 'ref' does not match 'mut'
-- bump_node(mut Node.{ val: 1 })       -- Error [E0410]: 'mut' requires an addressable writable place, or bind local first
-- bump_node(mut n0, 1)                 -- Error [E0314]: arity mismatch (expected 1, got 2)
-- fn bad_var(var x: int) -> () {}      -- Error [E0403]: 'var' parameter prohibited
-- fn bad_new_val(new x: int) -> () {}  -- Error [E0411]: 'new' prohibited on value type 'int'
-- let _ = consume_node(new n0)         -- Error [E0548]: 'n0' is not a construction-qualified 'new' binding
```

### Anonymous Functions and Trailing Closures

```ebnf
AnonFnExpr ::= "\" [ AnonParams ] "->" Expression
AnonParams ::= AnonParam { "," AnonParam } [ "," ]
AnonParam  ::= [ ParameterMode ] ( ValueName | "_" ) [ ":" TypeExpression ]
```

A `CallExpr` may pass its final callable argument as a trailing `AnonFnExpr` directly after `(...)`—or omit empty `()` altogether when the callable is the sole argument (`absorb_panic \-> { ... }`, `Async::scope \mut s -> { ... }`). Because `CallExpr` sits at Postfix Level 1, postfix `?` chains directly onto trailing-closure calls:

```ril
fn with_tx<T>(mut log: []str, body: fn(mut []str) @& -> Result<T, str>) &mut -> Result<T, str> {
    Array::push(mut log, "begin")
    let out = body(mut log)?
    Array::push(mut log, "commit")
    Ok out
}

fn execute() -> Result<int, str> {
    let mut log: []str = []
    let code = with_tx(mut log) \mut entries -> {
        Array::push(mut entries, "insert")
        Ok 200
    }?
    assert(log == ["begin", "insert", "commit"])
    Ok code
}
assert(execute() == Ok 200)
```

### Closures and Lexical Environments

Closures capture enclosing bindings by minimum required authority; returning or storing a closure that captures enclosing runtime variables or stateful lexical handlers requires `&capture` on the enclosing named function (`E0510`), and its `CallableType` carries `&up` (for immutable/observer environments) or requires a `mut` / `^mut` handle when mutating captured state:

```ril
type Cell = .{ var value: int }
type Step = fn() &up -> int

fn make_counter(^mut cell: Cell) &capture &^mut &return{^mut cell} -> new Step {
    \-> {
        cell.value += 1
        cell.value
    }
}

let mut c = Cell.{ value: 0 }
let ^mut step = make_counter(^mut c)
assert(step() == 1 && step() == 2 && c.value == 2)
```

---

## State and Provenance Tracking

```ebnf
StateAnnot            ::= StateClause { StateClause }
StateClause           ::= "&mut"
                        | "&^mut"
                        | "&capture"
                        | CapturedStateGroup
                        | ReturnDependencyGroup
CapturedStateGroup    ::= "&up{" StateItemList "}"
StateItemList         ::= StateItem { "," StateItem } [ "," ]
StateItem             ::= [ StateMode ] ValueName
StateMode             ::= "mut" | "^mut" | "ref"
ReturnDependencyGroup ::= "&return{" ReturnDependencyList "}"
ReturnDependencyList  ::= ReturnDependency { "," ReturnDependency } [ "," ]
ReturnDependency      ::= ( "ref" | "^mut" ) ValueName
```

### Local State Discharge, Parameter Mutation, and Sharing

- **Local Discharge**: Writes to local `var` / `let mut` allocations that do not escape the function are discharged locally; the function remains outwardly pure (`&{}`).
- **`&mut`**: Required on named functions that may mutate a `mut` or `^mut` parameter (`E0510`).
- **`&^mut`**: Required when a `^mut` parameter is retained into another parameter, closure environment, or non-root structure (`E0510`; root `-> ^mut(x) T` already accounts for its own return retention).
- **`&capture`**: Required when a named function returns or stores a newly created closure environment capturing runtime locals/parameters (`E0510`).

### State Groups and Captured Layers

Block-local named `fn` declarations that access enclosing local bindings spell `&up{...}` listing the captured outer bindings (`&up{limit}`, `&up{ref view}`, `&up{mut buf}`; malformed groups fail `E0538`). Module-level functions never carry `&up{...}` because module top-level forbids mutable/live state (`E0906`) and reading pure module constants (`let` / `meta let`) requires **no** state annotation.

```ril
let GLOBAL_FACTOR = 3                  -- Pure module constant

fn scale_all(xs: []int, offset: int) -> []int {
    fn transform(x: int) &up{offset} -> int {
        x * GLOBAL_FACTOR + offset     -- GLOBAL_FACTOR needs no '&up'; outer local 'offset' uses '&up{offset}'
    }
    -- fn bad_up(x: int) &up{ghost} -> int { x } -- Error [E0538]: unknown outer source 'ghost' in '&up{...}'
    let mut out: []int = []
    for xs as x {
        Array::push(mut out, transform(x))
    }
    out
}
assert(scale_all([1, 2], 4) == [7, 10])
```

### Exclusivity and Anti-Laundering Matrix

At every call and assignment, Ril enforces **Single-Writer or Multi-Observer Exclusivity** across potentially overlapping origin sets:

| Violation | Diagnostic |
| :--- | :---: |
| Writing through plain immutable or `ref` access, or binding immutable/`ref` data as `mut`/`^mut` | `E0520` |
| Destructuring pattern requesting `mut`/`^mut` from an immutable/`ref` subject or immutable field | `E0521` |
| Wrapping/coerce container element mode from `[T]` / `[ref]T` to `[mut]T` / `[^mut]T` | `E0522` |
| Passing two `mut` arguments (or `mut` + `^mut`) with potentially overlapping reachable origins | `E0523` |
| Passing `mut` alongside plain/`ref` observation of potentially overlapping reachable origins | `E0524` |
| Mutating a collection while iterating over it in `for` | `E0526` |
| Returning `mut` / `^mut` / `new` authority from immutable/`ref` or temporary `mut` sources | `E0528` |

```ril
type Box = .{ var n: int }
fn swap_add(mut a: Box, mut b: Box) &mut -> () { a.n += b.n }
fn observe_mut(mut a: Box, ref b: Box) &mut -> int { a.n += 1; b.n }

let mut x = Box.{ n: 1 }
-- swap_add(mut x, mut x)              -- Error [E0523]: overlapping mut-mut origins
-- let _ = observe_mut(mut x, ref x)   -- Error [E0524]: overlapping mut-ref hazard
-- let mut bad_elems: [mut]Box = [Box.{ n: 1 }] |> \xs: []Box -> xs -- Error [E0522]: container element mode laundering
let mut items = [1, 2, 3]
-- for ref items as v { Array::push(mut items, v) } -- Error [E0526]: mutating 'items' during 'for' iteration
```

---

## Algebraic Effects, Panic Containment, and Concurrency

### Effect Declarations and Handlers

Algebraic effects declare direct capability operations (`fn`) dispatched lexically to enclosing `with` handlers and returning directly to the call site (1-shot tail-resumptive semantics).

```ebnf
EffectDecl           ::= { MetaAttr } [ Visibility ] "eff" PascalCase [ GenericParams ]
                         "{" [ EffectMemberList ] "}"
EffectMemberList     ::= ( EffectSpread | EffectOpDecl ) { ( "," | Newline ) ( EffectSpread | EffectOpDecl ) } [ "," ]
EffectSpread         ::= ".." TypeReference
EffectOpDecl         ::= { MetaAttr } "fn" ValueName "(" [ ParameterTypeList ] ")" [ StateAnnot ] "->" ReturnType
EffectAnnot          ::= EffectClause { EffectClause }
EffectClause         ::= "@" EffectIdentifier
EffectIdentifier     ::= { PascalCase "::" } PascalCase [ GenericArgs ]
EffectOperationRef   ::= { PascalCase "::" } PascalCase [ GenericArgs ] "::" ValueName
WithStatement        ::= "with" HandlerSpec
HandlerSpec          ::= HandlerArm
                       | "{" [ HandlerArm { ( "," | Newline ) HandlerArm } [ "," ] ] "}"
HandlerArm           ::= EffectOperationRef "(" [ HandlerParameterList ] ")" "->" Expression
HandlerParameterList ::= HandlerParameter { "," HandlerParameter } [ "," ]
HandlerParameter     ::= [ "mut" | "^mut" | "ref" | "new" ] Pattern
```

| Handler rule | Requirement |
| :--- | :--- |
| Scope of `with` | `with` installs its handler arms over the remainder of the enclosing block; operations invoked inside an arm dispatch to outer handlers |
| Validation (`E0621`, `E0622`, `E0345`, `E0406`) | Arms must target declared `eff` operations (`E0621` on ordinary functions or `@Io`/`@Async`), without duplicate arms per `with` (`E0622`). Parameters must be irrefutable (`E0345`), non-`var` (`E0403`), and match the operation's declared parameter modes (`E0406`). Temporary `mut` operation authority ends when the arm returns |
| Discharge (`E0612`, `E0618`) | Covering all operations in a callee's known footprint (or all operations of an abstract `@Eff` parameter) discharges `@Eff`; uncovered operations remain required on named callers (`E0612`). Block-local `eff` declarations must be discharged before block exit (`E0618`) |
| Lexical closure capture | Closures created inside `with` capture active handlers needed for their residual `eff` operations (`&capture` / `&up` when capturing runtime state; pure stateless `fn` handlers reduce to `&{}`). Scoped resources or `Task` handles cannot escape via handler capture (`E0604`) |

```ril
eff Clock { fn now_ms() -> int }
eff Log { fn info(msg: str) -> () }

fn audit_event(name: str) @Clock @Log -> str {
    let ts = Clock::now_ms()
    Log::info("{ts}:{name}")
    "{ts}:{name}"
}

fn test_audit() -> () {
    let mut lines: []str = []
    with {
        Clock::now_ms() -> 1700,
        Log::info(msg)  -> Array::push(mut lines, msg),
        -- Clock::now_ms() -> 1800,           -- Error [E0622]: duplicate handler arm in single 'with'
        -- Io::println(s)  -> (),             -- Error [E0621]: '@Io' is a system effect, not a 'with' target
    }
    let res = audit_event("login")
    assert(res == "1700:login" && lines == ["1700:login"])
}
test_audit()
-- fn bad_eff() @int -> () {}                 -- Error [E0620]: 'int' is not a declared effect label
```

### Built-in System Effects

The prelude predeclares two operational system effect labels (`@Io` and `@Async`). Standard library modules `ril/io` and `ril/async` import cleanly via `use ril/io as SysIo` or selective imports (`use ril/async::{scope, spawn, join}`) without dual-identity symbol collisions; writing non-effect names after `@` fails `E0620`, and targeting `@Io` or `@Async` in `with ... ->` fails `E0621`.

| System effect | Purpose & discharge boundary |
| :--- | :--- |
| `@Io` | External host I/O, timers, filesystem/network access, and stateful `.d.ril` calls; serviced by the host runtime on `fn main` |
| `@Async` | Cooperative fiber suspension, channel waiting, structured nurseries, and cancellation checkpoints; serviced on `fn main` or discharged deterministically by `Async::run` |

### Panic Absorption with absorb_panic

`absorb_panic` contains synchronous defects behind an unwind-safe boundary, running active `let scoped` `close` handlers inside the protected closure before returning `Err (PanicError::Panicked info)`.

```ril
-- Prelude declarations:
pub opaque type PanicInfo = str
pub type PanicError { Panicked PanicInfo }

pub fn panic_message(info: PanicInfo) -> str
pub fn absorb_panic<T>(via action: fn() @& -> infer T) -> infer Result<T, PanicError>
```

```ril
fn parse_header(parts: []str) -> str { parts[1] }

fn isolated_parse(parts: []str) -> Result<str, PanicError> {
    absorb_panic \-> parse_header(parts)
}

assert(isolated_parse(["k", "v"]) == Ok "v")
let Err (PanicError::Panicked info) = isolated_parse(["only_one"]) else { panic("expected panic") }
assert(len(panic_message(info)) > 0)
let mut ext = [1, 2]
-- let _ = absorb_panic \-> Array::push(mut ext, 3) -- Error [E0608]: unwind-unsafe external 'mut' access inside 'absorb_panic'
```

| `absorb_panic` rule | Requirement |
| :--- | :--- |
| Unwind safety (`E0608`) | `action` must not observe or mutate external `mut`/`^mut`/`ref` state, access `.d.ril` `resource` handles, emit unhandled operational effects (including `@Io` / `@Async`), or leak mutable/scoped captures (`E0608`). Confined local `var` / `let mut` / `let scoped` state and locally handled pure `eff` operations are allowed |
| Sealed `PanicInfo` (`E0301`, `E0308`) | `PanicInfo` is an opaque prelude type (`E0301` on direct construction, `E0308` on representation penetration); `panic_message(info)` extracts the diagnostic message at run time (`E0810` in static evaluation) |
| Double-Fault termination | If a `let scoped` `close` handler panics while unwinding an earlier panic, the runtime terminates the OS process immediately without returning `Err` |

### Structured Async Concurrency and Channels

`ril/async` provides structured cooperative nurseries using lexical-region-bound `Scope` and `Task<T>` handles (carrying an internal static region $\sigma$ checked identically to `Draft<T>` confinement), alongside typed multi-producer single-consumer channels in `ril/async/channel`.

```ril
-- Canonical declarations in ril/async:
pub opaque type Scope
pub opaque type Task<T |> Sendable>
pub type Zip<A, B> = .{ via first: A, via second: B }
pub type TaskFault { ..PanicError, Cancelled }
pub type TimeoutError { Elapsed }

pub fn run<T |> Sendable>(via action: fn() @ -> infer T) -> infer T
pub fn yield_now() @Async -> ()
pub fn sleep_ms(ms: int) @Io @Async -> ()
pub fn is_cancelled() -> bool
pub fn uncancellable<T>(via action: fn() @& -> infer T) -> infer T
pub fn timeout_ms<T |> Sendable>(ms: int, work: fn() @ -> T) @Io @Async -> Result<T, TimeoutError>

pub fn scope<T>(via body: fn(mut Scope) @& -> infer T) @Async -> infer T
pub fn try_scope<T |> Sendable, E |> Sendable>(
    body: fn(mut Scope) @& -> Result<T, E>,
) @Async -> Result<T, E>
pub fn supervise<T |> Sendable>(work: fn() @ -> T) @Async -> Result<T, TaskFault>

pub fn spawn<T |> Sendable>(mut s: Scope, via work: fn() @ -> infer T) &mut -> new Task<T>
pub fn join<T |> Sendable>(mut s: Scope, via task: Task<T>) @Async &mut -> infer T
pub fn cancel<T |> Sendable>(mut s: Scope, new task: Task<T>) @Async &mut -> ?T
pub fn cancel_scope(mut s: Scope) &mut -> ()

pub fn zip<A |> Sendable, B |> Sendable>(
    via left: fn() @ -> infer A,
    via right: fn() @ -> infer B,
) @Async -> infer Zip<A, B>
pub fn try_zip<A |> Sendable, B |> Sendable, E |> Sendable>(
    left: fn() @ -> Result<A, E>,
    right: fn() @ -> Result<B, E>,
) @Async -> Result<(A, B), E>
pub fn map<T |> Sendable, U |> Sendable>(xs: []T, via work: fn(T) @ -> infer U) @Async -> infer []U
pub fn try_map<T |> Sendable, U |> Sendable, E |> Sendable>(
    xs: []T,
    work: fn(T) @ -> Result<U, E>,
) @Async -> Result<[]U, E>
pub fn race<T |> Sendable>(left: fn() @ -> T, right: fn() @ -> T) @Async -> T
```

```ril
-- Canonical declarations in ril/async/channel:
pub opaque type Sender<T |> Sendable>
pub opaque type Receiver<T |> Sendable>
pub type ChannelPair<T |> Sendable> = .{ mut tx: Sender<T>, mut rx: Receiver<T> }
pub type SendError<T> { Closed T }
pub type TrySendError<T> { Full T, Closed T }
pub type TryRecvError { Empty, Closed }

pub fn bounded<T |> Sendable>(capacity: int) -> new ChannelPair<T>
pub fn unbounded<T |> Sendable>() -> new ChannelPair<T>
pub fn clone<T |> Sendable>(ref tx: Sender<T>) -> new Sender<T>
pub fn send<T |> Sendable>(mut tx: Sender<T>, via item: T) @Async &mut -> infer Result<(), SendError<T>>
pub fn try_send<T |> Sendable>(mut tx: Sender<T>, via item: T) &mut -> infer Result<(), TrySendError<T>>
pub fn recv<T |> Sendable>(mut rx: Receiver<T>) @Async &mut -> new ?T
pub fn try_recv<T |> Sendable>(mut rx: Receiver<T>) &mut -> new Result<T, TryRecvError>
pub fn close<T |> Sendable>(new tx: Sender<T>) -> ()
pub fn close_recv<T |> Sendable>(new rx: Receiver<T>) -> ()
pub fn drain<T |> Sendable>(new rx: Receiver<T>, via f: fn(via T) @& -> ()) -> ()
```

```ril
use ril/async as AsyncRt
use ril/async/channel as Chan

fn sum_pipeline(limit: int) @Async -> int {
    AsyncRt::scope \mut s -> {
        let Chan::ChannelPair.{ mut tx, mut rx } = Chan::bounded(16)
        let _producer = AsyncRt::spawn(mut s) \-> {
            let mut sender = new tx
            for 1..=limit as i {
                match Chan::send(mut sender, i * i) {
                    Ok ()   -> (),
                    Err _   -> break,
                }
            }
            Chan::close(new sender)
        }
        -- var shared_cnt = 0
        -- let _ = AsyncRt::spawn(mut s) \-> { shared_cnt += 1 } -- Error [E0601]: cannot capture outer 'var' across fiber
        -- eff Trace { fn mark() -> () }
        -- var trace_n = 0
        -- with Trace::mark() -> { trace_n += 1 }
        -- let _ = AsyncRt::spawn(mut s) \-> Trace::mark()       -- Error [E0615]: stateful handler cannot cross fiber boundary
        var total = 0
        while let Some v = Chan::recv(mut rx) {
            total += v
        }
        total
    }
}
assert(AsyncRt::run(\-> sum_pipeline(4)) == 30)
```

| Concurrency & channel rule | Requirement |
| :--- | :--- |
| `Sendable` (`E0301`) | Admits value types, `.ril` shared objects without `ref`/`^mut` members whose constituents are `Sendable`, `Sender<U>` / `Receiver<U>`, and pure/stateless callables limited to `@Io`, `@Async`, and pure `fn` effects; rejects `Scope`, `Task`, `Draft`, `let scoped`, and `.d.ril` `resource` types |
| Cross-fiber isolation (`E0601`, `E0615`, `E0549`) | Fiber closures forbid `ref`, `mut`, `^mut`, `var`, or `scoped` captures (`E0601`) and stateful outer `fn` handlers (`E0615`); `@Io`, `@Async`, and pure stateless `fn` handlers cross fibers. Direct single-shot closures (`run`, `spawn`, `zip`, `try_zip`, `race`, `supervise`, `timeout_ms`) may move outer `new` bindings once (`E0549` on parent reuse) |
| Lexical region $\sigma$ (`E0604`) | Each `scope` / `try_scope` creates a fresh static region $\sigma$ shared by its `Scope` parameter and spawned `Task<T>` handles. Neither `Scope` nor `Task<T>` may escape `body` or cross into another nursery's `join`/`cancel` (`E0604`). Normal `scope` exit awaits unjoined tasks in reverse spawn order; `try_scope` `Err` cancels and drains siblings |
| `Result` inspection & supervision (`E0720`, `E0608`) | `Task<Result<T, E>>` must be `join`ed (inspecting its `Result`) or `cancel`ed (`E0720`); `Receiver<Result<T, E>>` requires `drain` (`close_recv` fails `E0720`); `try_*`, `race`, `timeout_ms`, and `supervise` reject nested `Result` payloads (`E0720`). `supervise` enforces unwind safety (`E0608`) |

---

## Compile-Time Computation and Introspection

### Static Type Values and Type Quotation

`Type<T>` is the exact static metatype representing type `T`; `<T>` quotes `T` as a static token value, and `<tok>` inside a type expression unquotes a static token back into a type. Bare `Type` in value annotations or bare type names in value expressions (`let x = int`) fail `E0319`.

```ebnf
TokenType        ::= "Type" "<" TypeExpression ">"
TypeFunctionExpr ::= "\" TypeFnParam { "," TypeFnParam } "->" Expression
TypeFnParam      ::= PascalCase [ TypeConstraint ]
                   | ValueName [ ":" TypeExpression ] { "|>" PipelineConstraint }
                   | ModeParamDecl
```

```ril
type Nullable = \T -> <?T>
type Unpack = \T -> {
    let tok: Type<T> = <T>
    <.{ item: <tok> }>
}
type OptInt = Nullable<int>
meta let _ = assert(<OptInt> == <?int> && <int> != <f64>)
-- let bad_bare = int                  -- Error [E0319]: bare type in value expression; write '<int>'
```

### Pure Type Functions and Result Restrictions

<a id="finite-evaluation-with-div"></a>

```ebnf
MetaLetDecl ::= [ Visibility ] "meta" "let" ( ValueName | "_" ) [ ":" TypeExpression ] "=" Expression
MetaFnDecl  ::= { MetaAttr } [ Visibility ] "meta" "fn" ValueName [ GenericParams ]
                "(" [ ParameterList ] ")" ReturnSpec Block
```

- **Pure Static Domain (`E0335`, `E0812`, `E0813`, `E0816`)**: `TypeFunctionExpr`, `meta fn`, and `meta let` evaluate in a pure compile-time environment with local `var`/`let mut`, loops, and recursion, forbidding `@Eff` / `&State` annotations (`E0335` on type functions, `E0813` on `meta fn`). `meta fn` cannot return `Type<T>` tokens (`E0812`). Run-time values, parameters, storage, and closures cannot materialize `Type<T>` (`E0816`).
- **Compiler Root Evaluation Budget (`E0811`, `E0830`, `E0831`)**: Every compile-time root evaluation (`type` application, pipeline guard, `meta let`, `meta(...)`, const generic argument, and compile-time folded `meta fn` call) executes under a configured deterministic step budget, charging 1 unit per function/closure entry and loop iteration. Exhausting the budget rejects compilation with uncatchable `E0811` (partial type previews in diagnostics are informational only). Failed static `assert` fails `E0830`; static `panic` or arithmetic defects fail `E0831`.

```ril
meta fn align_up(n: int, align: int) -> int {
    assert(n >= 0 && align > 0)
    ((n + align - 1) / align) * align
}
meta let PAGE = align_up(3000, 4096)
meta let _ = assert(PAGE == 4096)
-- meta let _ = assert(PAGE == 0)      -- Error [E0830]: static assertion failed
-- meta let _ = panic("boom")          -- Error [E0831]: static evaluation panicked
-- meta fn bad_tok() -> Type<int> { <int> } -- Error [E0812]: 'meta fn' cannot return 'Type<T>'
-- meta fn bad_io() @Io -> int { 1 }   -- Error [E0813]: 'meta fn' must be pure
-- fn rt_tok(t: Type<int>) -> () {}    -- Error [E0816]: runtime parameter cannot hold 'Type<int>'
-- type Spin = \T -> Spin<T>
-- type Boom = Spin<int>               -- Error [E0811]: compile-time evaluation budget exceeded
```

### Disjoint Call Families and Branch Pruning

| Evaluation context | Permitted calls (`E0810` otherwise) |
| :--- | :--- |
| `TypeEval` (type functions, guards) | Type functions, `meta fn`, static reflection, dual-phase built-ins (`len`, `assert`, `panic`) |
| `MetaValue` (`meta fn`, `meta let`, `meta(...)`) | `meta fn`, static reflection, dual-phase built-ins |
| `RunTime` (`fn`, closures) | Ordinary `fn`, foreign `.d.ril` `fn`, built-ins, plus direct saturated `meta fn` calls with static arguments (folded to immutable snapshots) |

In `RunTime` functions, `if` / `match` branches over `meta let` constants (such as `Platform::OS`) are fully type-, mode-, and effect-checked on all branches, then statically unreachable branches and `.d.ril` symbols referenced solely within them are pruned before code generation and linking. Static `match <T>` over a rigid type parameter checks each arm under its static token evidence and selects the matching arm at specialization. Negative static sizes/counts where nonnegative static values are required fail `E0815`.

### Static Introspection

```ebnf
TypeProjection            ::= PrimaryType "." ( FieldLabel | PascalCase | Digit+ | "(" Expression ")" )
MappedRecordType          ::= ".{" [ ModeModifier ] MappedComprehensionClause ":" TypeExpression "}"
MappedComprehensionClause ::= "[" Expression "as" Pattern "]"
ModeModifier              ::= MemberMode | ValueName
```

- **Constituent Projection (`T.(k)`)**: Projects field type `T.field` / `T.("field")` on transparent records, component type `T.0` / `T.(0)` on tuples, and payload type `T.Variant` / `T.("Variant")` on transparent sums (`()` for unit variants; `E0308` on sealed `opaque` types).
- **Record Coordinates & Sum Variants (`coords`, `variants`)**:
  - `coords(<T>) -> [](MemberMode, str)` enumerates `(mode, field_name)` pairs in UTF-8 byte order for transparent record types (`E0358` on non-records; `E0308` when sealed).
  - `variants(<T>) -> []str` enumerates deduplicated variant names in UTF-8 byte order for closed transparent sums (`E0301` on non-sums; `E0308` when sealed or open `..`).
- **Mapped Record Types (`.{ [m] [expr as pat]: Type }`)**: Comprehension keys must have type `str` (`E0341`), duplicate generated field names fail `E0210`, value-type fields with `mut`/`^mut`/`ref` modes fail `E0402`, and invalid mode sorts fail `E0356` / `E0357`.
- **Metadata Introspection (`ril/reflect`)**:
  - `Reflect::attrs<T, A>(target: Type<T>) -> []A`
  - `Reflect::field_attrs<T, A>(target: Type<T>, meta key: str |> Key<T>) -> []A`
  - `Reflect::variant_attrs<T, A>(target: Type<T>, meta variant: str) -> []A`

```ril
type Select = \T: .{ ..R }, keys: []str -> {
    let chosen = coords(<T>) |> Array::filter(\(_, k) -> Array::contains(keys, k))
    <.{ m [chosen as (m, k)]: T.(k) }>
}

type Model = .{ id: int, var title: str, mut rows: []int }
type Patch = Select<Model, ["title", "rows"]> -- .{ var title: str, mut rows: []int }
-- meta let _ = coords(<int>)          -- Error [E0358]: 'coords' requires a transparent record type
-- type BadMap = .{ [[1, 2] as k]: int } -- Error [E0341]: mapped record key must have type 'str'
-- type BadIdx = (int, str).(-1)       -- Error [E0815]: negative static tuple coordinate '-1'

fn read_field<T: .{ .. }>(via rec: T, meta key: str |> Key<T>) -> infer T.(key) {
    rec.(key)
}
let m = Model.{ id: 9, title: "init", rows: [1] }
assert(read_field(m, "title") == "init")
```

### Structural Type Pattern Matching

```ebnf
TypePattern           ::= "<" TypePatternInner ">"
TypePatternInner      ::= "_"
                        | "let" PascalCase
                        | TypeTuplePattern
                        | TypeRecordPattern
                        | TypeArrayPattern
                        | TypeMapPattern
                        | RigidNominalPattern
                        | PrimitivePattern
                        | LiteralPattern
TypeTuplePattern      ::= "(" ")"
                        | "(" TypePatternInner "," TypePatternTupleTail ")"
TypePatternTupleTail  ::= TypeRestPattern [ "," ]
                        | TypePatternInner { "," TypePatternInner } [ "," TypeRestPattern ] [ "," ]
TypeRecordPattern     ::= ".{" [ TypeRecordPatternList ] "}"
TypeRecordPatternList ::= TypeRestPattern [ "," ]
                        | TypePatternField { "," TypePatternField } [ "," TypeRestPattern ] [ "," ]
TypePatternField      ::= [ MemberMode ] FieldLabel ":" ( TypePatternInner | "_" )
                        | "let" PascalCase FieldLabel ":" ( TypePatternInner | "_" )
TypeRestPattern       ::= ".." [ PascalCase ]
TypeArrayPattern      ::= "[" [ ElementAccessMode ] "]" TypePatternInner
TypeMapPattern        ::= "[" TypePatternInner ":" [ ElementAccessMode ] TypePatternInner "]"
RigidNominalPattern   ::= { PascalCase "::" } RigidPatternSegment
RigidPatternSegment   ::= PascalCase [ "<" TypePatternArg { "," TypePatternArg } [ "," ] ">" ]
TypePatternArg        ::= TypePatternInner | MemberModeLiteral
PrimitivePattern      ::= PrimitiveType
```

`let U` binds a rigid type variable (or `MemberMode` in `let M field: ...`); bare `PascalCase` heads match rigid nominal/sum/opaque constructors (`E0306` on higher-kinded variable heads `<(let F)<let X>>`).

```ril
type UnwrapResult = \T -> match <T> {
    <Result<let OkT, _>> -> <OkT>,
    <?let Inner>         -> <Inner>,
    _                    -> <T>,
}
meta let _ = assert(<UnwrapResult<Result<int, str>>> == <int>)
```

---

## Modules, Program Execution, and Prelude

### Modules and Compilation Units

Ril enforces a strict **one-file-one-module** model with pure constant top-level initialization:

```ebnf
SourceFile ::= { RootItem Separator } [ RootItem ] EOF
RootItem   ::= ModuleItem | DeclUnitItem
ModuleItem ::= UseDecl | FunctionDecl | MetaFnDecl | MetaLetDecl
             | LetDecl | OpaqueTypeDecl | TypeDecl | NominalDecl
             | SumTypeDecl | EffectDecl
Visibility ::= "pub" [ "(" "pkg" ")" ]
```

| Compilation unit | Role & top-level rules |
| :--- | :--- |
| **Executable Root (`.ril`)** | Entry file of an executable build: unimportable (`E0208`), forbids `pub` / `pub(pkg)` (`E0905`), and requires a private root `fn main` (`E0903`, `E0904`) |
| **Library Module (`.ril`)** | Importable module named `to_pascal_case(file_stem)`; forbids `fn main` (`E0904`). Items default to file-private (`E0201`); files with zero `pub` items are `pub(pkg)`-sealed to external packages (`E0201`) |
| **External Interface (`.d.ril`)** | Bodyless foreign host declarations (`E0901` on bodies/`opaque`); forbids `fn main` (`E0904`) |
| **Top-Level Purity (`E0202`, `E0906`, `E0205`)** | Module top-level allows only pure deeply immutable constants (`let` and `meta let`). Mutable, shared, live `ref`, or `resource` top-level bindings (`var`, `let mut`, `let ^mut`, `let ref`) are prohibited (`E0906`); impure initializers fail `E0202`; top-level `?` fails `E0205` |

```ril
-- File: math/circle.ril
pub let PI = 3.141592653589793
pub(pkg) let INTERNAL_EPS = 1.0e-9
type Hidden = .{ r: f64 }

pub fn area(r: f64) -> f64 { PI * r * r } -- Zero '&up' needed for pure module constant 'PI'
-- pub fn leak() -> Hidden { Hidden.{ r: 1.0 } } -- Error [E0910]: 'pub' signature leaks private type 'Hidden'
-- var global_hits = 0                    -- Error [E0906]: top-level mutable state is prohibited
-- let boot_ts = Clock::now()             -- Error [E0202]: top-level initializer must be pure
```

### Module Imports and Visibility

```ebnf
UseDecl     ::= [ Visibility ] "use" FilePath [ "as" PascalCase ]
              | [ Visibility ] "use" ModulePath "::" ( "{" ImportList "}" | "*" | ImportItem )
PackageRoot ::= "pkg" | "ril" | SnakeCase
FilePath    ::= PackageRoot "/" SnakeCase { "/" SnakeCase }
ModulePath  ::= FilePath | PascalCase
ImportList  ::= ImportItem { "," ImportItem } [ "," ]
ImportItem  ::= Identifier [ "as" Identifier ]
```

- **Package Roots (`E0208`, `E0209`)**: `pkg/...` resolves inside the current package, `ril/...` resolves standard-library modules, and `<dep>/...` resolves mounted dependencies (`E0208` on missing module or bare single-segment path; `E0209` on absent member). Unaliased `use pkg/http/server` binds `Server` (`to_pascal_case("server")`).
- **Visibility Lattice & Interface Consistency (`E0201`, `E0910`)**: `private < pub(pkg) < pub`. Re-exports (`pub use`) cannot widen target visibility (`E0201`). Any `pub` or `pub(pkg)` declaration's expanded signature, non-opaque fields/variants, `TypeFunctionExpr` body, `close` cleanup function, and unhandled `@Eff` must have visibility $\ge$ the declaration's own visibility (`E0910`; `pub opaque` internal representations remain private).

```ril
use pkg/math/circle as Circle
-- use pkg/math/missing                -- Error [E0208]: module 'pkg/math/missing' not found
-- use pkg/math/circle::nonexistent    -- Error [E0209]: 'nonexistent' not found in 'Circle'
-- let _ = Circle::Hidden.{ r: 1.0 }   -- Error [E0201]: 'Hidden' is private to 'Circle'
```

### Program Entry Point

```ril
use ril/file as File

fn main() @Io @Async -> Result<(), str> {
    let raw = File::read("config.json")?
    if raw == "" { Err "empty config" } else { Ok () }
}
-- Missing 'fn main' in executable root       -- Error [E0903]
-- fn main(argc: int) -> int { argc }         -- Error [E0904]: invalid 'main' signature
-- pub let ROOT_EXPORT = 1                    -- Error [E0905]: 'pub' prohibited in executable root
```

`main` must be a non-public, non-generic ordinary `fn` in the executable root taking `()` and returning `()` or `Result<(), str>` (`E0903` if missing, `E0904` if malformed). It may declare `@Io` and `@Async` (`E0612` on unhandled user-defined `eff`). Returning `()` / `Ok ()` exits `0`; returning `Err msg` prints `msg` + `\n` to stderr and exits `1`.

### Prelude Scope

The ambient prelude predeclares primitive types, `Option<T>` (`Some T`, `None`), `Result<T, E>` (`Ok T`, `Err E`), `Set<T>`, `PanicInfo`, `PanicError`, `MemberMode`, `Draft<T>`, `@Io`, `@Async`, static guards `SharedObject`, `Sendable`, `LenTarget`, `Key`, and core modules `Array`, `Map`, `Set`, `String`, `Bytes`, `Numeric`, `Reflect`. Explicit imports (`use ril/io`, `use ril/file`, `use ril/os`, `use ril/async`, `use ril/async/channel`, `use ril/parallel`, `use ril/platform`, `use ril/math`, `use ril/crypto`) bring system, concurrency, parallel, and platform APIs into scope.

#### Built-in Foundational Operations

| Built-in | Canonical signature | Phase & contract |
| :--- | :--- | :--- |
| `len` | `pub fn len<T \|> LenTarget>(via item: T) -> int` | Dual-phase: scalar count of `str`, byte count of `bytes`, element/entry count of `[]T`, `[K: V]`, `Set<T>` (admits `ref` on collections at run time; `E0401` on `ref str`) |
| `clone` | `pub fn clone<T \|> SharedObject>(via value: T) -> new T` | Run-time: deep copy of `SharedObject` (via snapshot or `ref`) into isolated `new T` (`E0301` on value/`resource` types, `E0530` on live closures) |
| `derive` | `pub fn derive<T \|> SharedObject>(base: T, recipe: fn(mut Draft<T>) @& -> ()) -> T` | Run-time: path-targeted functional update on immutable `SharedObject` (`E0536`, `E0607`) |
| `absorb_panic` | `pub fn absorb_panic<T>(via action: fn() @& -> infer T) -> infer Result<T, PanicError>` | Run-time: unwind-safe panic containment (`E0608`) |
| `panic_message` | `pub fn panic_message(info: PanicInfo) -> str` | Run-time: extracts human-readable message from `PanicInfo` (`E0810` in static eval) |
| `type_name` | `pub meta fn type_name<T>(token: Type<T>) -> str` | Static only: diagnostic display string of `T` |
| `coords` | `pub meta fn coords<T>(token: Type<T>) -> [](MemberMode, str)` | Static only: `(mode, field)` pairs of transparent record `T` (`E0358` non-record, `E0308` sealed) |
| `variants` | `pub meta fn variants<T>(token: Type<T>) -> []str` | Static only: variant tags of closed transparent sum `T` (`E0301` non-sum, `E0308` sealed/open) |
| `panic` | `pub fn panic(message: str) -> never` | Dual-phase: LIFO panic unwinding at run time; `E0831` in static eval |
| `assert` | `pub fn assert(condition: bool) -> ()` | Dual-phase: panics when `false` at run time; `E0830` when `false` in static eval |
| `print` / `println` | `pub fn print(text: str) @Io -> ()`<br>`pub fn println(text: str) @Io -> ()` | Run-time (`@Io`): writes UTF-8 text (plus `\n` for `println`) to stdout |

### Mandatory Inspection of Fallible Results

Every produced `Result<T, E>` carries a mandatory static inspection obligation (`E0720`): before normal scope exit, it must be matched (`match`, `if let`, `let ... else`), propagated (`?`), handled (`??`), or returned. Discarding a `Result` as an expression statement, binding it to `_`, or overwriting its last variable without tag inspection fails `E0720`.

```ril
fn write_entry(line: str) @Io -> Result<(), str> {
    println(line)
    Ok ()
}

fn handle_log() @Io -> Result<(), str> {
    -- write_entry("dropped")             -- Error [E0720]: unused fallible Result
    -- let _ = write_entry("ignored")     -- Error [E0720]: '_' does not inspect Result
    write_entry("propagated")?            -- OK: propagated via '?'
    write_entry("fallback") ?? \_e -> ()  -- OK: handled via '??'
    Ok ()
}
```

---

## Diagnostic Error Codes Summary

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
| **`E0125`** | [`AdjacentConstructorArgumentError`](#syntactic-diagnostic-conditions) |

### Names, Initialization, and Field Identity

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0201`** | [`PrivateItemAccessError`](#module-imports-and-visibility) |
| **`E0202`** | [`TopLevelSideEffectError`](#modules-and-compilation-units) |
| **`E0203`** | [`DuplicateDeclarationError`](#identifiers-and-casing-invariants) |
| **`E0204`** | [`UnresolvedIdentifierError`](#identifiers-and-casing-invariants) |
| **`E0205`** | [`QuestionMarkOutsideFunctionError`](#pipeline-and-fallible-operators) |
| **`E0206`** | [`AmbiguousConstructorError`](#identifiers-and-casing-invariants) |
| **`E0207`** | [`UseBeforeInitializationError`](#block-expressions-and-local-declarations) |
| **`E0208`** | [`ModuleNotFoundError`](#module-imports-and-visibility) |
| **`E0209`** | [`UnresolvedModuleMemberError`](#module-imports-and-visibility) |
| **`E0210`** | [`DuplicateFieldError`](#record-types-and-row-polymorphism) |
| **`E0212`** | [`OverlappingRowFieldError`](#record-types-and-row-polymorphism) |
| **`E0213`** | [`ConflictingVariantSpreadError`](#sum-variant-spreading-and-subset-conversion) |

### Types, Expressions, Generics, and Patterns

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0301`** | [`TypeMismatchError`](#diagnostic-classification) |
| **`E0302`** | [`UnexpectedFieldError`](#record-types-and-row-polymorphism) |
| **`E0303`** | [`NonExhaustiveMatchError`](#pattern-matching) |
| **`E0304`** | [`UnreachableMatchArmError`](#pattern-matching) |
| **`E0305`** | [`NominalTypeMismatchError`](#nominal-opaque-and-resource-types) |
| **`E0306`** | [`KindMismatchError`](#generic-parameters-and-value-sorts) |
| **`E0307`** | [`MissingFieldError`](#record-types-and-row-polymorphism) |
| **`E0308`** | [`OpaqueBoundaryViolationError`](#nominal-opaque-and-resource-types) |
| **`E0309`** | [`VacuousBindingError`](#guarded-bindings) |
| **`E0312`** | [`TupleIndexOutOfBoundsError`](#array-map-set-and-tuple-types) |
| **`E0313`** | [`CyclicTypeAliasError`](#definitional-equality-and-recursive-types) |
| **`E0314`** | [`ArityMismatchError`](#parameter-modes-and-caller-obligations) |
| **`E0315`** | [`EscapingLocalNominalTypeError`](#block-expressions-and-local-declarations) |
| **`E0318`** | [`LiteralTypeProhibitedError`](#generic-parameters-and-value-sorts) |
| **`E0319`** | [`BareTypeInExpressionContextError`](#static-type-values-and-type-quotation) |
| **`E0321`** | [`NormallyCompletingElseError`](#guarded-bindings) |
| **`E0322`** | [`WildcardExpressionError`](#identifiers-and-casing-invariants) |
| **`E0323`** | [`ConstGenericSortMismatchError`](#generic-parameters-and-value-sorts) |
| **`E0324`** | [`DynamicRecordIndexProhibitedError`](#record-types-and-row-polymorphism) |
| **`E0326`** | [`LiteralOutOfRangeError`](#numeric-literals) |
| **`E0327`** | [`UnsupportedOperandTypeError`](#arithmetic-bitwise-relational-and-logical-operators) |
| **`E0328`** | [`InvalidCollectionKeyTypeError`](#arithmetic-bitwise-relational-and-logical-operators) |
| **`E0330`** | [`BareEffectTypeAliasError`](#type-definition-boundaries) |
| **`E0331`** | [`BareStateAnnotationTypeAliasError`](#type-definition-boundaries) |
| **`E0332`** | [`VariantComputationAnnotationError`](#type-definition-boundaries) |
| **`E0333`** | [`FieldComputationAnnotationError`](#type-definition-boundaries) |
| **`E0334`** | [`GenericComputationConstraintError`](#type-definition-boundaries) |
| **`E0335`** | [`TypeFunctionComputationAnnotationError`](#type-definition-boundaries) |
| **`E0336`** | [`UnknownFieldError`](#record-types-and-row-polymorphism) |
| **`E0337`** | [`NonProductProjectionError`](#indexing-slicing-and-static-coordinate-projection) |
| **`E0338`** | [`NonCallableInvocationError`](#pipeline-and-fallible-operators) |
| **`E0340`** | [`GenericArityMismatchError`](#generic-parameters-and-value-sorts) |
| **`E0341`** | [`InvalidRecordKeySortError`](#static-introspection) |
| **`E0344`** | [`InsufficientTypeInformationError`](#generic-parameters-and-value-sorts) |
| **`E0345`** | [`RefutablePatternError`](#guarded-bindings) |
| **`E0346`** | [`OrPatternBindingMismatchError`](#pattern-matching) |
| **`E0347`** | [`DuplicatePatternBindingError`](#pattern-matching) |
| **`E0348`** | [`InvalidRangePatternError`](#pattern-matching) |
| **`E0349`** | [`InvalidPatternExpressionError`](#pattern-matching) |
| **`E0350`** | [`NonBooleanConditionError`](#conditional-and-loop-expressions) |
| **`E0351`** | [`IncompatibleBranchTypesError`](#structural-joins-and-normal-continuations) |
| **`E0352`** | [`InvalidIndexTargetError`](#indexing-slicing-and-static-coordinate-projection) |
| **`E0355`** | [`NonIterableValueError`](#conditional-and-loop-expressions) |
| **`E0356`** | [`InvalidModeSortError`](#array-map-set-and-tuple-types) |
| **`E0357`** | [`IncompatibleMemberModeError`](#record-types-and-row-polymorphism) |
| **`E0358`** | [`InvalidModeProjectionTargetError`](#static-introspection) |
| **`E0361`** | [`DivisionOrShiftDomainError`](#arithmetic-bitwise-relational-and-logical-operators) |

### Parameters and Argument Modes

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0401`** | [`ValueTypeReferenceParameterError`](#value-types) |
| **`E0402`** | [`ValueTypeReferenceModeError`](#value-types) |
| **`E0403`** | [`VarParameterProhibitedError`](#parameter-modes-and-caller-obligations) |
| **`E0405`** | [`MissingArgumentModeMarkerError`](#parameter-modes-and-caller-obligations) |
| **`E0406`** | [`InvalidArgumentModeError`](#parameter-modes-and-caller-obligations) |
| **`E0407`** | [`CallableParameterModeMismatchError`](#callable-contract-matching) |
| **`E0410`** | [`InvalidMutableArgumentTargetError`](#parameter-modes-and-caller-obligations) |
| **`E0411`** | [`InvalidConstructionParameterError`](#parameter-modes-and-caller-obligations) |
| **`E0412`** | [`InvalidModeInferencePlacementError`](#access-mode-inference-with-via-and-infer) |

### Bindings, State, Access Modes, and Resource Contracts

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0501`** | [`ImmutableReassignmentError`](#binding-modes-and-storage-matrix) |
| **`E0502`** | [`PinnedHandleReassignmentError`](#binding-modes-and-storage-matrix) |
| **`E0503`** | [`InvalidAssignmentTargetError`](#record-construction-and-assignments) |
| **`E0510`** | [`MissingStateAnnotationError`](#mandatory-contract-inference-and-completion) |
| **`E0520`** | [`MutabilityLaunderingError`](#exclusivity-and-anti-laundering-matrix) |
| **`E0521`** | [`DestructureMutabilityLaunderingError`](#exclusivity-and-anti-laundering-matrix) |
| **`E0522`** | [`ContainerMutabilityLaunderingError`](#exclusivity-and-anti-laundering-matrix) |
| **`E0523`** | [`MutMutAliasingConflictError`](#exclusivity-and-anti-laundering-matrix) |
| **`E0524`** | [`ReadMutAliasingHazardError`](#exclusivity-and-anti-laundering-matrix) |
| **`E0526`** | [`CollectionMutationDuringIterationError`](#exclusivity-and-anti-laundering-matrix) |
| **`E0528`** | [`ReturnMutabilityLaunderingError`](#exclusivity-and-anti-laundering-matrix) |
| **`E0530`** | [`IllegalNonClonableAuthorityError`](#deep-immutability) |
| **`E0531`** | [`InvalidRefOriginError`](#subtyping-reception-and-contract-compatibility) |
| **`E0532`** | [`ReassignableScopedResourceError`](#scoped-resource-bindings) |
| **`E0534`** | [`CallableContractMismatchError`](#callable-contract-matching) |
| **`E0535`** | [`NonImmutableBindingError`](#deep-immutability) |
| **`E0536`** | [`InvalidDeriveInputError`](#functional-updates-via-derive) |
| **`E0537`** | [`LiveArrayInvalidationError`](#indexing-slicing-and-static-coordinate-projection) |
| **`E0538`** | [`InvalidStateSourceGroupError`](#state-groups-and-captured-layers) |
| **`E0541`** | [`InvalidScopedCleanupContractError`](#scoped-resource-bindings) |
| **`E0543`** | [`UnanchoredRefOriginError`](#subtyping-reception-and-contract-compatibility) |
| **`E0544`** | [`MissingInferredFunctionAnnotationError`](#mandatory-contract-inference-and-completion) |
| **`E0545`** | [`InvalidReturnSourceContractError`](#return-construction-access-modes-and-sources) |
| **`E0546`** | [`InvalidNewReturnContractError`](#return-construction-access-modes-and-sources) |
| **`E0547`** | [`InvalidOpenRowPlacementError`](#closed-and-open-callable-rows) |
| **`E0548`** | [`InvalidConstructionInputError`](#parameter-modes-and-caller-obligations) |
| **`E0549`** | [`EndedConstructionAuthorityAccessError`](#construction-qualified-locals-and-mode-preserving-reception) |
| **`E0550`** | [`RedundantModeViaError`](#inference-domains-and-contract-completion) |
| **`E0551`** | [`InvalidPatternDecompositionError`](#pattern-matching) |
| **`E0552`** | [`IncompatibleInferredInterfaceError`](#inferred-interfaces-and-callable-families) |

### Effects, Concurrency, and Escape

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0601`** | [`CrossTaskAuthorityError`](#structured-async-concurrency-and-channels) |
| **`E0604`** | [`ScopedOrRegionEscapeError`](#scoped-resource-bindings); [Structured Async Concurrency and Channels](#structured-async-concurrency-and-channels) |
| **`E0607`** | [`DeriveDraftEscapeError`](#functional-updates-via-derive) |
| **`E0608`** | [`UnwindUnsafePanicBoundaryError`](#panic-absorption-with-absorb_panic) |
| **`E0612`** | [`UnhandledEffectError`](#effect-declarations-and-handlers) |
| **`E0613`** | [`ValueEffectAnnotationError`](#type-definition-boundaries) |
| **`E0615`** | [`ConcurrentEffectBoundaryError`](#structured-async-concurrency-and-channels) |
| **`E0618`** | [`UndischargedLocalEffectError`](#block-expressions-and-local-declarations) |
| **`E0620`** | [`InvalidEffectLabelError`](#built-in-system-effects) |
| **`E0621`** | [`InvalidHandlerTargetError`](#effect-declarations-and-handlers) |
| **`E0622`** | [`DuplicateHandlerOperationError`](#effect-declarations-and-handlers) |

### Declaration Contexts, Control Flow, and Fallible Values

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0701`** | [`ChainedAssignmentProhibitedError`](#record-construction-and-assignments) |
| **`E0707`** | [`InvalidControlTransferContextError`](#conditional-and-loop-expressions) |
| **`E0708`** | [`InvalidMetadataPlacementError`](#declaration-metadata-attributes) |
| **`E0710`** | [`IllegalControlTransferInFallbackError`](#pipeline-and-fallible-operators) |
| **`E0711`** | [`InvalidResultFallbackError`](#pipeline-and-fallible-operators) |
| **`E0712`** | [`InvalidPropagationOperandError`](#pipeline-and-fallible-operators) |
| **`E0713`** | [`IncompatiblePropagationTargetError`](#pipeline-and-fallible-operators) |
| **`E0714`** | [`InvalidFallbackOperandError`](#pipeline-and-fallible-operators) |
| **`E0715`** | [`InvalidSafeAccessReceiverError`](#pipeline-and-fallible-operators) |
| **`E0720`** | [`UnusedFallibleResultError`](#mandatory-inspection-of-fallible-results) |

### Static Computation

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0810`** | [`CallFamilyViolationError`](#disjoint-call-families-and-branch-pruning) |
| **`E0811`** | [`CompileTimeBudgetExceededError`](#pure-type-functions-and-result-restrictions) |
| **`E0812`** | [`MetaTypeReturnProhibitedError`](#pure-type-functions-and-result-restrictions) |
| **`E0813`** | [`MetaComputationAnnotationError`](#pure-type-functions-and-result-restrictions) |
| **`E0814`** | [`StaticValueRequiredError`](#generic-parameters-and-value-sorts) |
| **`E0815`** | [`InvalidStaticValueError`](#disjoint-call-families-and-branch-pruning) |
| **`E0816`** | [`RuntimeTypeTokenProhibitedError`](#pure-type-functions-and-result-restrictions) |
| **`E0830`** | [`MetaAssertionFailedError`](#pure-type-functions-and-result-restrictions) |
| **`E0831`** | [`StaticEvaluationPanicError`](#pure-type-functions-and-result-restrictions) |

### Module Forms, Entry Points, and External Contracts

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0901`** | [`BodyInDeclModuleError`](#external-interface-declarations) |
| **`E0902`** | [`MissingBodyInStandardModuleError`](#external-interface-declarations) |
| **`E0903`** | [`MissingEntryPointError`](#program-entry-point) |
| **`E0904`** | [`InvalidEntryPointError`](#program-entry-point) |
| **`E0905`** | [`RootUnitExportProhibitedError`](#modules-and-compilation-units) |
| **`E0906`** | [`TopLevelMutableStateProhibitedError`](#modules-and-compilation-units) |
| **`E0907`** | [`ForeignStructuralFieldPenetrationError`](#external-interface-declarations) |
| **`E0908`** | [`UnsupportedExternalAuthorityContractError`](#external-interface-declarations) |
| **`E0909`** | [`BuiltinSignatureMismatchError`](#named-function-declarations-and-contrast-matrix) |
| **`E0910`** | [`ExportedVisibilityLeakError`](#module-imports-and-visibility) |
