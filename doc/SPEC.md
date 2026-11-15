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
| Reachable authority use | `var` requires reachable slot replacement, `mut` requires writable/consuming use, `^mut` parameters require surviving retention, and named state annotations must be minimal (`E0527`, `E0529`) |
| `where` / guards | Dual-tier `where` hoists helper declarations (`type`, `fn`, `meta fn`, block `eff`); `\|>` contracts validate static types and fallible runtime values |
| `is` / narrowing | `is` tests tags, shapes, ranges, and subsets without binding names, refining stable paths across branches (`==` tests symmetric same-type equality) |
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
    - [Nominal, Type Alias, and Opaque Types](#nominal-type-alias-and-opaque-types)
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
    - [Generic Parameters, Defaults, and Value Sorts](#generic-parameters-defaults-and-value-sorts)
    - [Type Definition Boundaries](#type-definition-boundaries)
  - [Static Semantics and Type Kernel](#static-semantics-and-type-kernel)
    - [Static Contexts and Judgment Forms](#static-contexts-and-judgment-forms)
    - [Type Formation and Binding](#type-formation-and-binding)
    - [Definitional Equality and Recursive Types](#definitional-equality-and-recursive-types)
    - [Subtyping, Reception, and Contract Compatibility](#subtyping-reception-and-contract-compatibility)
    - [Bidirectional Expression Checking](#bidirectional-expression-checking)
      - [Anonymous Generalization and Fixed Storage](#anonymous-generalization-and-fixed-storage)
    - [Structural Joins and Normal Continuations](#structural-joins-and-normal-continuations)
    - [Generic Evidence and Definition Checking](#generic-evidence-and-definition-checking)
    - [Authority, Calls, and Contract Operations](#authority-calls-and-contract-operations)
    - [Recursive Summaries and Grounded Inference](#recursive-summaries-and-grounded-inference)
    - [Phase Checking and Static Evaluation](#phase-checking-and-static-evaluation)
    - [Semantic Interfaces and Diagnostic Boundaries](#semantic-interfaces-and-diagnostic-boundaries)
  - [Declarations and Bindings](#declarations-and-bindings)
    - [Binding Modes and Storage Matrix](#binding-modes-and-storage-matrix)
      - [Reachable Authority Use](#reachable-authority-use)
    - [Construction-Qualified Locals and Mode-Preserving Reception](#construction-qualified-locals-and-mode-preserving-reception)
    - [Immutable, Mutable, Shared, and Reference Bindings](#immutable-mutable-shared-and-reference-bindings)
    - [Scoped Resource Bindings](#scoped-resource-bindings)
    - [Declaration Metadata Attributes](#declaration-metadata-attributes)
    - [External Interface Declarations](#external-interface-declarations)
  - [Expressions and Operators](#expressions-and-operators)
    - [Expression Grammar and Precedence](#expression-grammar-and-precedence)
    - [Arithmetic, Bitwise, Relational, and Logical Operators](#arithmetic-bitwise-relational-and-logical-operators)
      - [Value Tests with is](#value-tests-with-is)
    - [Indexing, Slicing, and Static Coordinate Projection](#indexing-slicing-and-static-coordinate-projection)
    - [Text and Byte Operations](#text-and-byte-operations)
    - [Pipeline and Fallible Operators](#pipeline-and-fallible-operators)
    - [Record Construction and Assignments](#record-construction-and-assignments)
  - [Control Flow and Pattern Matching](#control-flow-and-pattern-matching)
    - [Block Expressions and Local Declarations](#block-expressions-and-local-declarations)
    - [Conditional and Loop Expressions](#conditional-and-loop-expressions)
    - [Guarded Bindings](#guarded-bindings)
    - [Pattern Matching](#pattern-matching)
    - [Flow-Sensitive Type Narrowing](#flow-sensitive-type-narrowing)
  - [Functions, Closures, and Callables](#functions-closures-and-callables)
    - [Named Function Declarations and Contrast Matrix](#named-function-declarations-and-contrast-matrix)
      - [Dual-Tier Where Invariants](#dual-tier-where-invariants)
      - [Signature Value Contracts](#signature-value-contracts)
    - [Callable Contracts](#callable-contracts)
      - [Mandatory Contract Inference and Completion](#mandatory-contract-inference-and-completion)
      - [Closed and Open Callable Rows](#closed-and-open-callable-rows)
      - [Callable Contract Matching](#callable-contract-matching)
    - [Return Construction, Access Modes, and Sources](#return-construction-access-modes-and-sources)
    - [Parameter Modes, Caller Obligations, and Defaults](#parameter-modes-caller-obligations-and-defaults)
      - [Default Parameters and Named Arguments](#default-parameters-and-named-arguments)
    - [Anonymous Functions, Trailing Closures, and Projection Accessors](#anonymous-functions-trailing-closures-and-projection-accessors)
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
    - [Parameters, Argument Modes, and Defaults](#parameters-argument-modes-and-defaults)
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
| Authority independence | Object liveness grants no write authority; `with let` deterministic cleanup is independent of GC |

### Failure Model and Purity

<a id="termination-and-halt-contracts"></a>

Ril separates expected domain failures from programming defects:

1. **Recoverable Errors (`Result<T, E>` and `?T`)**: Carried as explicit values. Every `Result` must be inspected, propagated via `?`, or handled via `??` (`E0720`).
2. **Defects (`panic` / `assert`)**: Trigger deterministic LIFO stack unwinding, running active `with let` cleanup handlers without requiring signature annotations. Unwind-safe boundaries (`absorb_panic`, `Async::supervise`) convert panics into `Result` values carrying `PanicInfo`.
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
| Secondary panic inside `with let` cleanup during active panic/cancel unwinding | Immediate Double-Fault OS process termination (bypasses `absorb_panic`) |
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

- **Line continues** after binary/pipeline/fallback/test operators (`+`, `-`, `*`, `/`, `%`, `&`, `|`, `^`, `<<`, `>>`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `is`, `&&`, `||`, `|>`, `as`, `??`, `=`, `+=`, `-=`, `*=`, `/=`, `%=`, `&=`, `|=`, `^=`, `<<=`, `>>=`, `->`, `:`, `,`, `.`, `?.`, `::`) or inside unclosed `( ... )`, `[ ... ]`, `.{ ... }`.
- **Line continues** before postfix `.field`, `?.field`, `|>`, `as`, `??`, or signature `where` on the next line (`with` is never a line-continuation token; type-level `with <fn_name>` cleanup clauses must appear on the same line as the end of the type declaration). Inside `{ ... }`, `where` opens the trailing `BlockWhereClause`.
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

Ril enforces lexically disjoint ASCII identifier casing roles (`E0101` on wrong role, `E0102` on malformed casing such as un-title-cased acronyms, `camelCase`, or consecutive underscores):

```ebnf
Identifier         ::= PascalCase | ValueName | ScreamingSnakeCase
ValueName          ::= SnakeCase | UnderscoreName
PascalCase         ::= [A-Z] { [a-z0-9] } { [A-Z] [a-z0-9]+ }
SnakeCase          ::= [a-z] { [a-z0-9] } { "_" [a-z0-9]+ }
ScreamingSnakeCase ::= [A-Z] { "_" [A-Z0-9]+ }
                     | [A-Z] [A-Z0-9]+ { "_" [A-Z0-9]+ }
UnderscoreName     ::= "_" [a-z] { [a-z0-9] } { "_" [a-z0-9]+ }
Wildcard           ::= "_"
QualifiedName      ::= { "Super" "::" } { PascalCase "::" } Identifier
```

- **Acronym Title-Casing & Casing Partition (`E0101`, `E0102`)**:
  - `PascalCase` starts with `[A-Z]`, contains no `_`, and title-cases acronyms as regular words (`T`, `U`, `User`, `UserId`, `HttpServer`, `JsonParser`, `Sha256` are valid `PascalCase`; adjacent uppercase letters such as `HTTPServer`, `UserID`, or `AB` fail `E0102`, and multi-letter all-caps names such as `PI`, `OS`, `MAX_CONN` are `ScreamingSnakeCase` constants).
  - Single-letter uppercase names (`T`, `U`, `K`, `V`, `M`) are `PascalCase` type/mode/variant identifiers; `ScreamingSnakeCase` constants require `_` or $\ge 2$ uppercase/digit characters (`PI`, `N_MAX`, `A_1`).
- **Closed Casing Roles (`E0101`, `E0103`)**:
  - `PascalCase`: Types (`type`), sum variants, nominal constructors, effects (`eff`), module/`sub` namespaces (`Array`, `Super`), and type/mode/row generic parameters.
  - `SnakeCase` / `UnderscoreName` (`ValueName`): Local variables, parameters, functions (`fn`, `meta fn`), record fields, effect operations, const generic parameters, and module file path segments (`pkg/http/server`).
  - `ScreamingSnakeCase`: Reserved exclusively for compile-time constants (`meta let`) and module/`sub` top-level immutable constants (`let`) (`E0101` in local bindings or parameters; `E0103` in pattern binding positions).
  - `Wildcard` (`_`): Discard binder/pattern only; reading `_` as a value expression fails `E0322`.
- **Name Resolution (`E0203`, `E0204`, `E0206`)**:
  - Same-scope duplicate declarations fail `E0203`. `Type` and `Super` are protected names and cannot be redeclared, bound, or aliased (`E0203`).
  - Unresolved names fail `E0204`. Unqualified variant constructors imported or declared from multiple sums in the same scope fail `E0206` unless qualified (`SumA::Tag`).

```ril
type HttpServer = .{ port: int }       -- OK: title-cased acronym PascalCase
let local_port = 8080                  -- OK: snake_case local binding
meta let MAX_RETRY = 3                 -- OK: SCREAMING_SNAKE_CASE constant
-- type HTTPServer = .{ port: int }    -- Error [E0102]: acronym must be title-cased ('HttpServer')
-- let badCamel = 1                    -- Error [E0102]: mixed camelCase prohibited
-- let user__name = "Ada"              -- Error [E0102]: consecutive underscores prohibited
-- meta let max_retry = 3              -- Error [E0101]: 'meta let' requires SCREAMING_SNAKE_CASE
-- type user_doc = .{ id: int }        -- Error [E0101]: type identifier must be PascalCase
-- let Some USER_ID = Some 1           -- Error [E0103]: uppercase identifier in pattern binder position
-- meta let MAX_RETRY = 4              -- Error [E0203]: duplicate declaration in same scope
-- let ghost = missing_name            -- Error [E0204]: unresolved identifier
-- type A { Dup }; type B { Dup }
-- let ambig = Dup                     -- Error [E0206]: ambiguous unqualified constructor; write 'A::Dup'
-- let _ = 1; let bad_wild = _         -- Error [E0322]: '_' cannot be read as an expression
```

### Keywords

The following 30 reserved syntax keywords cannot be used as identifiers or field labels (`E0113`):

```text
as       break    continue eff      else     false    fn       for
if       infer    is       let      match    meta     mut      new
opaque   pub      ref      return   sub      true     type     typeof
use      var      via      where    while    with
```

- **Protected Names (`bool`, `int`, `f64`, `str`, `bytes`, `never`, `Type`, `Super`)**: Primitive type names cannot be used as identifiers or field labels (`E0113`), `Type` and `Super` cannot be redeclared or shadowed (`E0203`), and bare type names in runtime value expressions fail `E0319` (write `<int>`, `<never>`).
- **Contextual Identifiers (`pkg`, `ril`, `capture`, `up`)**: Ordinary `SnakeCase` identifiers in expressions, bindings, parameters, and record fields (`let pkg = "core"`), recognized contextually inside `pub(pkg)`, `use pkg/...`, `use ril/...`, `&capture`, and `&up` / `&up{...}`.

```ril
let pkg = "core"                       -- OK: contextual outside pub(pkg) and use pkg/...
let capture = true                     -- OK: contextual outside &capture
-- let where = 1                       -- Error [E0113]: reserved keyword
-- let opaque = 1                      -- Error [E0113]: reserved keyword
-- let via = 1                         -- Error [E0113]: reserved keyword
-- type BadField = .{ is: bool }       -- Error [E0113]: reserved keyword as field label
-- let int = 0                         -- Error [E0113]: intrinsic primitive type name
```

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
RawStringLiteral  ::= { "#" } "`" { RawCharacter } "`" { "#" }
ByteStringLiteral ::= 'bytes"' { ByteCharacter | ByteEscape } '"'
                    | "bytes" RawByteLiteral
RawByteLiteral    ::= { "#" } "`" { RawByteCharacter } "`" { "#" }
Interpolation     ::= "{" Expression "}"
```

- **String escapes (`E0107`, `E0108`, `E0109`)**: `\\`, `\"`, `\n`, `\r`, `\t`, `\0`, and `\u{H+}` (1–6 hex digits denoting a valid Unicode scalar value, `E0109` on surrogates or `> 0x10FFFF`). Raw strings open with $k \ge 0$ `#` characters plus `` ` `` and close only on `` ` `` plus $k$ `#` characters (`E0107` if unclosed), performing no escape or interpolation processing (normalizing multiline `CRLF` to `LF`).
- **Byte literals (`E0110`)**: `bytes"..."` admits ASCII `0x20..0x7E` (excluding unescaped `"` and `\`) plus `\\`, `\"`, `\n`, `\r`, `\t`, `\0`, and `\xHH` (exact 2 hex digits). `` bytes`...` `` / `` bytes#`...`# `` admit raw ASCII bytes with no escapes. Non-ASCII characters in byte literals fail `E0110`.

```ril
let host = "ril.dev"
let port = 443
let url = "https://{host}:{port}/v1"
let raw_path = `C:\data\ril`
let raw_quote = #`contains `backticks` and {literal_braces}`#
let magic = bytes"\x89PNG\r\n\x1a\n"
let http_line = bytes`GET / HTTP/1.1`
assert(url == "https://ril.dev:443/v1" && len(magic) == 8 && len(http_line) == 14)
-- let bad_unterm = #`unterminated`    -- Error [E0107]: requires closing '`#'
-- let bad_esc = "\q"                  -- Error [E0108]: unknown escape
-- let bad_uni = "\u{D800}"            -- Error [E0109]: UTF-16 surrogate is not a Unicode scalar
-- let bad_byte = bytes"λ"             -- Error [E0110]: non-ASCII byte literal character
-- let bad_raw_b = bytes`λ`            -- Error [E0110]: non-ASCII raw byte literal character
-- let bad_interp = "val={}"           -- Error [E0112]: empty interpolation expression
```

### Boolean and Unit Literals

```ebnf
Literal ::= IntLiteral | FloatLiteral | StringLiteral | RawStringLiteral
          | ByteStringLiteral | "true" | "false" | "(" ")"
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
                 | "?" TypeExpression
                 | "typeof" UnaryExpr
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

Record types, values, patterns, tests, and mapped types uniformly use `.{...}`. Record fields may declare slot/access `MemberMode` modifiers (`var`, `mut`, `^mut`, `ref`, `var mut`, `var ^mut`, `var ref`), and root record declarations in `.ril` may attach pure default expressions (`= expr`).

```ebnf
RecordType      ::= ".{" [ RecordFieldList ] "}"
RecordFieldList ::= RecordTail
                  | RecordField { "," RecordField } [ "," RecordTail ] [ "," ]
RecordField     ::= { MetaAttr } [ MemberMode ] FieldLabel ":" TypeExpression [ "=" Expression ]
FieldLabel      ::= ValueName
RecordTail      ::= ".." [ PascalCase ]
MemberMode      ::= "var" [ "mut" | "^mut" | "ref" ]
                  | "mut" | "^mut" | "ref"
```

- **Closed Records**: Exact field set (written order irrelevant). Duplicate labels fail `E0210`; missing fields without defaults fail `E0307`; unexpected fields fail `E0302`; reading an unknown field fails `E0336`; dynamic bracket indexing `rec[k]` fails `E0324`.
- **Row Polymorphism (`..R` / `..`)**: Opens a record type in generic bounds, type aliases, or direct Ril callable parameters (`type WithId<R> = .{ id: int, ..R }`, `fn f(r: .{ id: int, .. }) -> int`). Non-record row instantiations fail `E0306`; overlapping explicit labels and row remainder labels fail `E0212`; incompatible field modes fail `E0357`.
- **Root Record Field Defaults (`E0359`, `E0404`, `E0408`, `E0409`)**: `= expr` is permitted only on root fields of `.ril` `TypeDecl`, `OpaqueTypeDecl`, and `NominalDecl` record declarations (`E0359` on nested, parameter, anonymous, or sum-payload records, and `E0901` in `.d.ril`). Defaults forbid `mut`/`^mut`/`ref`/`via` field modes (`E0404`; plain and `var` value/immutable fields are allowed), forbid self or forward field references (`E0408`), and must be pure (`E0409`). At construction `ServerCfg.{ host: "ril.dev" }`, explicit fields evaluate left-to-right first, then omitted defaults evaluate in declaration order. Transparent `TypeDecl` aliases supply defaults only when constructed through the alias name (`Cfg.{ ... }`).

```ril
type WithId<R> = .{ id: int, ..R }
type ServerCfg = .{ host: str, port: int = 8080, var retries: int = 3 }

fn get_id(item: .{ id: int, .. }) -> int { item.id }
let cfg = ServerCfg.{ host: "ril.dev" }
assert(get_id(.{ id: 7, active: true }) == 7 && cfg.port == 8080 && cfg.retries == 3)
-- type BadDup = .{ id: int, id: int }               -- Error [E0210]: duplicate field label
-- type BadOverlap = WithId<.{ id: str }>            -- Error [E0212]: row remainder overlaps 'id'
-- type BadTail = WithId<int>                        -- Error [E0306]: row tail requires a record type
-- let bad_extra: .{ id: int } = .{ id: 1, x: 2 }    -- Error [E0302]: unexpected field 'x'
-- let bad_miss: ServerCfg = .{ host: "a" }          -- Error [E0307]: structural literal omits 'ServerCfg' prefix
-- let bad_unknown = cfg.email                       -- Error [E0336]: unknown field 'email'
-- let bad_dyn = cfg["host"]                         -- Error [E0324]: dynamic bracket indexing prohibited on records
-- let bad_mode: .{ var x: int } = .{ x: 1 }         -- Error [E0357]: incompatible member mode
-- type BadNested = .{ inner: .{ x: int = 1 } }      -- Error [E0359]: field default only on root declaration
-- type BadMutDef = .{ mut items: []int = [] }       -- Error [E0404]: writable field mode forbids default
-- type BadFwd = .{ a: int = b, b: int = 1 }         -- Error [E0408]: forward field reference in default
-- eff Rng { fn next() -> int }
-- type BadImpure = .{ seed: int = Rng::next() }     -- Error [E0409]: field default must be pure
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

- **Arrays & Maps**: Default element mode is deeply immutable (`[]T`, `[K: V]`). Element modes admit `mut`, `^mut`, `ref`, `via`, or `MemberMode` parameters without `var` slot modifiers (`E0356`). Map keys `K` and `Set<T>` elements must support structural value equality (`E0328`). Map key reads require safe lookup `m?[k] -> ?V` (`E0352` on `m[k]` reads or `m[k] += v`; direct assignment `m[k] = v` inserts or replaces). Collection lengths and sequence indices have type `int`.
- **Tuples**: Zero-element `()` or $\ge 2$ elements `(A, B)`. Single-element `(T)` is grouping, never a 1-tuple. Tuple slots are strictly immutable; mutable multi-field aggregates use records (`.{ var a: A, mut b: B }`). Out-of-bounds tuple projection `pair.5` fails `E0312`.

```ril
let xs: []int = [10, 20, 30]
let mut table: [str: int] = ["ok": 200]
table["not_found"] = 404
let pair: (int, str) = (1, "one")
assert(xs[0] == 10 && table?["ok"] == Some 200 && pair.1 == "one")
-- let bad_map_read = table["ok"]      -- Error [E0352]: map lookup requires safe indexing 'table?["ok"]'
-- let bad_idx = pair.2                -- Error [E0312]: tuple index out of bounds
-- type BadKey = [f64: int]            -- Error [E0328]: 'f64' is not a valid map/set key type
-- type BadElem = [var][]int           -- Error [E0356]: array element mode forbids 'var'
```

### Sum Types and Variant Spreading

Every sum variant declares either no payload (unit tag) or **one** payload type (`T`, `(A, B)`, `.{...}`, `[]T`, etc.).

```ebnf
SumTypeDecl       ::= ( TypeDeclHead | OpaqueTypeHead ) "{" VariantDeclList "}" [ WithCleanupClause ]
VariantDeclList   ::= VariantDeclItem { "," VariantDeclItem } [ "," ]
VariantDeclItem   ::= VariantSpread | VariantDecl
VariantSpread     ::= ".." TypeReference
VariantDecl       ::= { MetaAttr } PascalCase [ TypeExpression ]
                    | ".."
WithCleanupClause ::= "with" ValueName
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
3. **Pattern & `is` Subset Narrowing (`SubType as binder`, `..SubType`, `e is ..SubType`)**: Matches any variant belonging to `SubType`.

```ril
pub type DbErr { Deadlock, ConnLost str }
pub type AuthErr { MissingToken, Expired }
pub type ApiErr { ..DbErr, ..AuthErr, BadInput str }
-- type ConflictErr { ..DbErr, ConnLost int } -- Error [E0213]: conflicting payload for 'ConnLost'

fn handle_err(err: ApiErr) -> (int, str) {
    match err {
        DbErr as db    -> (503, match db { Deadlock -> "retry", ConnLost h -> h }),
        ..AuthErr      -> (401, "unauthorized"),
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

### Nominal, Type Alias, and Opaque Types

Ril defines four `.ril` type declaration forms alongside `.d.ril` opaque host handles:

```ebnf
TypeDecl       ::= TypeDeclHead "=" ( TypeExpression | TypeFunctionExpr )
OpaqueTypeDecl ::= OpaqueTypeHead "=" TypeExpression [ WithCleanupClause ]
NominalDecl    ::= ( TypeDeclHead | OpaqueTypeHead ) [ TypeExpression ] [ WithCleanupClause ]
TypeDeclHead   ::= { MetaAttr } [ Visibility ] "type" PascalCase [ GenericParams ]
OpaqueTypeHead ::= { MetaAttr } [ Visibility ] "opaque" "type" PascalCase [ GenericParams ]
LocalTypeDecl  ::= TypeDecl | OpaqueTypeDecl | NominalDecl | SumTypeDecl
```

| Form | Declaration | Identity, construction & unwrapping |
| :--- | :--- | :--- |
| Transparent alias | `type Point = .{ x: f64, y: f64 }` | `=` makes it definitionally equal to its target everywhere (`E0313` on alias cycles; `E0708` on `meta(...)`) |
| Scope-opaque type | `pub opaque type Token = str` | Transparent inside its exact defining `sub` or root file; distinct sealed type outside (`E0301` / `E0308`, including child/parent `sub`s). Bodyless `opaque type` in `.ril` requires a registered built-in/stdlib identity (`E0902` otherwise) |
| Nominal type / marker | `pub type Marker`<br>`pub type UserId int`<br>`pub type Tag .{ k: str }` | No `=`: distinct type everywhere (`E0305`). Unit `Marker` is a value; non-record `UserId 42` uses space; nominal record `Tag.{ k: "a" }` attaches `.{`. Prelude `inner(w)` unwraps accessible nominal wrappers (`inner(UserId 42) == 42`, `inner(Marker) == ()`; `E0308` if `opaque` outside defining scope) |
| Sum type | `pub type Res<T, E> { Ok T, Err E }` | Tagged union (`opaque` seals variant construction/matching outside exact defining scope, `E0308`) |
| Foreign opaque handle (`.d.ril`) | `pub opaque type OwnedFd with close` | Exclusive host-managed affine handle (`E0907` on structural penetration, `E0908` on unannotated snapshot signature): forbids `clone`, `derive`, `==`, plain `let` freezing, `^mut`, and `[M]` arrays; admits `new`, `let mut`, `mut`, `ref`, and `with let` |

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
pub fn close_conn(new _c: Conn<Connected>) -> () {}

let uid = UserId 42
assert(inner(uid) == 42 && inner(Disconnected) == ())
let mut c0 = open_raw()
let mut c1 = dial(new c0, 3)
close_conn(new c1)
-- let _ = dial(new c0, 4)             -- Error [E0549]: 'c0' ended at handoff
-- let bad_nom: OrgId = UserId 1       -- Error [E0305]: distinct nominal types 'OrgId' vs 'UserId'
-- type Cyc = Cyc                      -- Error [E0313]: cyclic transparent type alias
-- Outside Conn's defining scope:
-- let bad_peek = c1.fd                -- Error [E0308]: opaque representation is sealed outside defining scope
```

### Deep Immutability

Plain `let`, `var`, default parameters, and plain collection elements hold **deeply immutable snapshots**: no surviving writable alias (`mut` / `^mut`) and no live `ref` dependency may reach the stored graph (`E0535`). When an immutable value is received for a schema containing `var`/`mut`/`ref` members, those member modes remain inactive on the frozen snapshot (`E0520` on write).

`clone(value)` / `clone(ref live)` deep-copies any ordinary `SharedObject` graph (preserving internal aliasing and cycles within the copied graph) into an isolated `new T` (`E0301` on value types, `.d.ril` `opaque` handles, or callables; `E0530` when containing non-clonable live/mutable closure environments).

```ril
type Cell = .{ var count: int }
let mut live = Cell.{ count: 1 }
-- let bad_snap = live                 -- Error [E0535]: 'live' has surviving write authority
let snap = clone(ref live)             -- OK: isolated snapshot frozen into 'let'
let mut copy = clone(snap)             -- OK: 'clone' returns isolated 'new Cell'
copy.count = 99
assert(live.count == 1 && snap.count == 1 && copy.count == 99)
let ^mut shared = live
let ^mut holder = .{ mut cb: \-> { shared.count += 1; shared.count } }
assert((holder.cb)() == 2)
-- let _ = clone(ref holder)           -- Error [E0530]: cannot clone structure holding mutable closure authority
```

### Type Identity and Subtyping

Ril has **no implicit numeric widening** and **no structural width subtyping** on closed records (`E0301`). Subtyping $S <: T$ holds only for:
1. Reflexivity / definitional equality ($S \equiv T$, expanding transparent `type A = B` aliases).
2. Bottom type (`never <: T` for every well-formed `T`).
3. Covariant immutable optionals (`?S <: ?T` when $S <: T$; mutable/invariant containers require `S ≡ T`).
4. Callable contract subsumption (`MatchCallable`: contravariant parameter types, covariant return type, identical concrete access modes, and bounded effect/state rows).

### Complete Provenance and Required Annotations

Access modes, origins, state writes, environment captures, and effects are static judgments verified modularly across call boundaries and erased before code generation. Named functions spell their required minimal operational effects (`@Eff`) and non-pure state/provenance clauses (`&mut`, `&^mut`, `&capture`, `&up{...}`, `&return{...}`); anonymous closures infer full contracts automatically.

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
assert(view.count == 2)
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
    d.profile.tags |> mut Array::push("admin")
}
assert(base.profile.email == "a@ril.dev" && len(base.profile.tags) == 1)
assert(next.profile.email == "b@ril.dev" && next.profile.tags == ["core", "admin"])
-- let _ = 42 |> derive \mut _d -> ()            -- Error [E0536]: value type 'int' is not a SharedObject
-- var leak: ?(fn() &up -> str) = None
-- let _ = base |> derive \mut d -> { leak = Some \-> d.profile.email } -- Error [E0607]: Draft escapes recipe
```

| `derive` rule | Requirement |
| :--- | :--- |
| Root eligibility (`E0536`) | `base` must be a deeply immutable `SharedObject` (including accessible `opaque`/nominal shared objects); value types, `.d.ril` `opaque` handles, and live `mut`/`^mut`/`ref` roots fail `E0536` |
| `Draft<T>` confinement (`E0607`) | `Draft<T>` is bound to the recipe activation; draft handles, derived `ref`/`mut` paths, and capturing closures cannot escape the recipe (`E0607`) |
| Inserted values (`E0535`) | Assigned values must be deeply immutable or recipe-local fresh allocations free of external surviving writers (`E0535`) |
| Fixed shape (`E0336`, `E0312`) | Preserves record fields, tuple arity, and sum tags of `T`; forwards recipe operational effects and external state obligations |

### Generic Parameters, Defaults, and Value Sorts

Declarations admit rigid type parameters (`T`), compile-time value parameters (`cap: int`), and member-mode parameters (`M: MemberMode`). Type declarations (`type`, `opaque type`, and `TypeFunctionExpr`) additionally admit trailing default generic arguments (`E0316` if non-trailing, `E0320` on self/forward parameter reference; generic defaults on `fn` or `meta fn` are prohibited with `E0317`).

```ebnf
GenericParams         ::= "<" GenericParamDecl { "," GenericParamDecl } [ "," ] ">"
GenericParamDecl      ::= TypeParamDecl | ConstParamDecl | ModeParamDecl
TypeParamDecl         ::= PascalCase [ TypeConstraint ] [ "=" TypeExpression ]
TypeConstraint        ::= [ ":" TypeSort ] { "|>" PipelineConstraint }
TypeSort              ::= TypeSetSort | "Type" | RecordConstraint
TypeSetSort           ::= TypeReference "|" TypeReference { "|" TypeReference }
PipelineConstraint    ::= QualifiedName [ GenericArgs ]
ConstParamDecl        ::= ValueName ":" TypeExpression { "|>" PipelineConstraint } [ "=" Expression ]
RecordConstraint      ::= ".{" RecordConstraintField { "," RecordConstraintField } "," RecordTail "}"
                        | ".{" RecordTail "}"
RecordConstraintField ::= [ MemberMode ] FieldLabel ":" TypeExpression
ModeParamDecl         ::= PascalCase ":" ModeSortReference [ "=" MemberModeLiteral ]
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
type Chunk<T = int, cap: int |> Positive = 64, M: MemberMode = mut> = .{ [M] data: []T }
type DefaultChunk = Chunk<>
-- type BadOrder<T = int, U> = (T, U)            -- Error [E0316]: non-trailing generic default
-- fn bad_fn_def<T = int>(x: T) -> T { x }       -- Error [E0317]: generic defaults prohibited on functions
-- type BadGenFwd<A = B, B = int> = (A, B)       -- Error [E0320]: forward generic default reference 'B'
-- type BadChunk = Chunk<int, 0>                 -- Error [E0323]: fails guard 'Positive'
-- type BadSort = Chunk<int, str>                -- Error [E0323]: type supplied to const parameter
-- type BadUnion = int | str                     -- Error [E0318]: untagged union cannot be used as storage type
-- type BadArity = Option<int, str>              -- Error [E0340]: generic arity mismatch
-- let bad_empty = []                            -- Error [E0344]: element type cannot be determined
-- fn dyn_cap(n: int) -> () { let _: Chunk<int, n> = .{ data: [] } } -- Error [E0814]: non-static const arg
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
| `D` | Package (`pkg`) and module scopes, visibility/opacity, type `with` cleanup contracts, primitive/foreign signatures |
| `Delta` | Rigid type, const, member-mode, and record-row parameters |
| `Gamma` | Value bindings, slot/access modes, callable contracts, lexical region tags ($\sigma$) |
| `Phi` | Declared generic constraints and static `match <T>` branch evidence |
| `F` | Origin sets, active construction paths (`new`), aliasing/exclusivity, `Result` inspection obligations |
| `q` | Phase: `TypeEval`, `MetaValue`, or `RunTime` |

### Type Formation and Binding

- **K-TYPE**: Primitives, rigid parameters in `Delta`, well-sorted generic applications, distinct-label records, arity-$0$ or $\ge 2$ immutable-slot tuples, valid-mode collections, complete `CallableType` contracts, `Type<A>`, and forward-evaluated computed types form valid types.
- **K-TYPE-ROW**: `.{ fields L, ..R }` is well-formed iff `R` instantiates to a record row whose labels are disjoint from `L` (`E0306` on non-record `R`, `E0212` on overlapping labels).

### Definitional Equality and Recursive Types

- **K-EQ**: Transparent `type A = B` aliases expand directly; cyclic transparent aliases without nominal or sum indirection fail `E0313`. Records compare equal up to field reordering when labels, types, and `MemberMode`s match. Nominal, sum, and `opaque` types (both `.ril` and `.d.ril`) compare by declaration identity and static argument equivalence (canonical IEEE bits for `f64` where `-0.0 != 0.0` and NaNs agree; structural value equivalence for collections/records; definitional target identity for `Type<A>`).
- **Opacity Scope**: Inside its exact defining `sub` or root `.ril` file, `opaque type A = Rep` permits representation projection and construction while retaining `A`'s declaration identity in `Type<A>` and exported interfaces; outside that exact scope (including child or parent `sub`s), `Rep` is sealed (`E0301`, `E0308`).

### Subtyping, Reception, and Contract Compatibility

- **K-RECV (`Receive`)**: Validates receiving an expression of synthesized mode/origins into a target binding, parameter, element, or return schema:
  - Plain immutable receivers require deeply immutable inputs free of surviving writers and live `ref` origins (`E0535`).
  - Exclusive `mut` receivers require unshared writable sources or fresh `new` allocations (`E0510` on unacknowledged shared aliases, `E0520` on immutable/`ref` sources, `E0406` on `^mut` marker).
  - Shared `^mut` receivers require writable sources and explicit `^mut` acknowledgment on existing roots (`E0510`).
  - Persistent `let ref` / `var ref` receivers require pinned `let mut` origins, existing `ref` handles, or immutable shared objects (`E0531` on reassignable `var` roots, `E0543` on unanchored fresh allocations or borrowed sum-subset re-wraps).
  - `new` receivers require fresh construction results or explicit `new x` handoff ending `x` (`E0548`, `E0549`).

### Bidirectional Expression Checking

- **Synthesis & Checking (`K-EXPR`)**: Operands evaluate and check left-to-right; contextual expected types propagate inward to empty array/map literals (`[]`), anonymous closures (`\x -> ...`), sum constructors (`Ok 1` under `Result<int, str>`), and `if`/`match` arms (`E0344` if any required type/const instantiation or monomorphic storage schema remains undetermined).

#### Anonymous Generalization and Fixed Storage

- **K-ANON**: Local `let` bindings of pure anonymous functions generalize unresolved unconstrained parameters and structural row constraints (`let identity = \x -> x`, `let get_id = \r -> r.id`), specializing independently at each call site. When an unannotated closure contains multiple `?` sites over `Result<_, E_i>`, its inferred error type selects the unique greatest sum $E_{\max} \in \{E_i\}$ under $\preceq_{\text{sum}}$ (`E0344` if no single member dominates and no contextual `CallableType` supplies the target sum). Mutable storage slots (`var`, array/map elements, record fields) and escaping runtime values require fixed monomorphic schemas (`E0344` if unanchored).

```ril
let identity = \x -> x
let read_id = \r -> r.id
assert(identity(42) == 42 && identity("ril") == "ril")
assert(read_id(.{ id: 1, name: "a" }) + read_id(.{ id: 2, ok: true }) == 3)
-- var poly_slot = \x -> x              -- Error [E0344]: reassignable storage requires a fixed monomorphic type
```

### Structural Joins and Normal Continuations

- **K-JOIN**: Branches with no normal continuation (`never` from `return`, `break`, `continue`, `panic`, `?`, `...`) contribute their prior side effects and obligations without constraining the join result type. Normally completing branches must join to a common type (`E0351` on incompatible types).
- **K-TYPE-RESULT**: In `TypeFunctionExpr` bodies, different static branches may return `Type<A>` and `Type<B>` tokens for distinct well-formed types `A` and `B`; closed evaluation yields the selected branch's single rigid token.

### Generic Evidence and Definition Checking

- **K-GEN**: Generic function bodies typecheck once at definition time against all admitted instantiations (`E0301` on unproved operations).
- **K-GEN-MATCH**: Transparent unguarded type-pattern decision trees (`\T -> match <T> { <int> | <f64> -> <T>, _ -> <never> }`) supply path-specific positive/negative type evidence to constrained generic bodies.

### Authority, Calls, and Contract Operations

- **K-CALL**: Call preparation evaluates explicit arguments left-to-right (followed by omitted parameter defaults in declaration order and signature parameter guards), freezes the call-entry reachability graph, immediately ends any `new arg` source path (`E0549` on later arguments reading `arg`), checks cross-argument aliasing exclusivity (`E0523`, `E0524`), and instantiates return origins (`ref(x)`, `^mut(x)`, `&return{...}`).
- **Pure Constant Origins**: Reading module/`sub`-level pure immutable constants (`let` or ordinary-valued `meta let`) introduces **zero** `&up` state or capture obligations.

### Recursive Summaries and Grounded Inference

- **K-FIX**: Mutually recursive functions and `via` mode families compute least fixed-point summaries over actual writes, captures, escapes, and unhandled operational effects. Freshness (`new`), isolation, local state discharge, and reachable authority use (`E0527` — self-forwarding `fn f(mut c: Cell) -> () { f(mut c) }` is ungrounded) require grounded non-circular proofs.

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

- **K-IFACE**: Compiled module interfaces retain normalized parameter/return schemas, parameter labels and defaults, `via` mode correlations, `with` cleanup contracts, `Sendable` / `SharedObject` representation facts across `opaque` boundaries, operational-effect footprints, and minimal provenance relations.

---

## Declarations and Bindings

```ebnf
LetDecl               ::= [ Visibility ] "let" ( ScreamingSnakeCase | Pattern ) [ ":" TypeExpression ] "=" Expression
LetMutDecl            ::= "let" "mut" Pattern [ ":" TypeExpression ] "=" Expression
SharedMutDecl         ::= ( "let" | "var" ) "^mut" ( ValueName | Wildcard ) [ ":" TypeExpression ] "=" Expression
VarDecl               ::= "var" ( ValueName | Wildcard ) [ ":" TypeExpression ] "=" Expression
VarMutDecl            ::= "var" "mut" ( ValueName | Wildcard ) [ ":" TypeExpression ] "=" Expression
LetRefDecl            ::= "let" "ref" Pattern [ ":" TypeExpression ] "=" Expression
VarRefDecl            ::= "var" "ref" ( ValueName | Wildcard ) [ ":" TypeExpression ] "=" Expression
ModePreservingBinding ::= "let" "via" Pattern [ ":" TypeExpression ] "=" Expression
WithLetDecl           ::= "with" "let" [ "mut" ] ( ValueName | Wildcard ) [ ":" TypeExpression ] "=" Expression
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

#### Reachable Authority Use

Every declared mutable slot, writable handle, shared-authority marker, and mutable parameter must have a statically reachable use after dead-branch pruning (`E0527: UnusedAuthorityError`; statically unreachable `if false { ... }` writes and ungrounded recursive self-forwarding do not count):

| Declared authority | Required reachable use (`E0527` when absent) |
| :--- | :--- |
| `var x` / `var ref x` | Reachable slot replacement (`x = ...` or compound assignment) |
| `let mut x` / `mut p` parameter | Reachable interior write, `mut`/`^mut` forwarding to a grounded writer, or `new` handoff (read-only signature guards do not count) |
| `var mut x` | Both reachable slot replacement and reachable writable/consuming use |
| `let ^mut x` / `var ^mut x` | Both shared writable reception (on initialization or replacement) and reachable writable use |
| `^mut p` parameter / handler binder | Surviving writable retention beyond temporary call/arm duration (root `-> ^mut(p)`, `&return{^mut p}`, `&^mut` store, or `&capture`; mutating `p` alone without retention fails `E0527`) |
| `^mut expr` sharing marker | Target receiver requires shared writable authority (`let ref r = ^mut src` fails `E0527`) |
| `with let mut x` / `with let mut _` | Satisfied automatically when type `T`'s `with <fn_name>` takes `new Self` or `mut Self`; requires a body write when `with <fn_name>` takes `ref Self` |
| Contextual callback `_` / `_name` | Named `fn` and unconstrained standalone closures enforce `E0527` on `_` / `_name`; an `AnonFnExpr` checked directly against an expected `CallableType` (`derive \mut _d -> ()`, `run_hook(mut c) \mut _ -> ()`) or `with Eff::op(mut _) -> ...` where `mut`/`^mut` is mandated by the target signature exempts `_` and `_name` |

Declared record/collection member schemas (`type Box = .{ var count: int }`) carry no independent `E0527` obligation.

```ril
type Cell = .{ var count: int }

fn run_hook(mut c: Cell, hook: fn(mut Cell) &mut -> ()) &mut -> () { hook(mut c) }
fn keep(^mut c: Cell) -> ^mut(c) Cell { c }

let mut c = Cell.{ count: 5 }
run_hook(mut c) \mut _ -> ()                   -- OK: contextual callback '_' exempt from E0527
let ^mut kept = keep(^mut c)
kept.count += 1
assert(c.count == 6)
-- var idle = 1                                -- Error [E0527]: 'var' never reassigned on any reachable path
-- fn read_only(mut x: Cell) -> int { x.count } -- Error [E0527]: 'mut' parameter has no writable use
-- fn temp_only(^mut x: Cell) &mut -> () { x.count += 1 } -- Error [E0527]: '^mut' parameter is never retained
-- fn loop_mut(mut x: Cell) -> () { loop_mut(mut x) }     -- Error [E0527]: ungrounded recursive forwarding
-- let ^mut fresh = Cell.{ count: 0 }; fresh.count += 1   -- Error [E0527]: unshared root needs 'let mut', not '^mut'
-- let ref bad_mark = ^mut c                   -- Error [E0527]: redundant '^mut' marker for 'ref' receiver
```

### Construction-Qualified Locals and Mode-Preserving Reception

A pinned `let mut` local initialized from a constructor, `clone(...)`, `-> new T` call, or `new src` handoff retains static `new` construction qualification as long as no `^mut` alias or escaping reference is formed. Passing `new x` transfers ownership in-place and immediately ends `x` and any derived views (`E0549`).

```ril
type Buffer = .{ mut items: []int }

fn build_buffer() -> new Buffer {
    let mut b = Buffer.{ items: [] }
    b.items |> mut Array::push(1)
    b                                  -- OK: 'b' retains 'new' qualification; local write discharges
}

let mut b1 = build_buffer()
let mut b2 = new b1                    -- Handoff ends 'b1'
-- let n = len(ref b1.items)           -- Error [E0549]: 'b1' ended at handoff
b2.items |> mut Array::push(2)
assert(len(ref b2.items) == 2)
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
draft.title = "v3"
assert(reader.title == "v3")
-- reader.title = "v4"                 -- Error [E0520]: 'ref' grants no write authority
-- draft = Doc.{ title: "new" }        -- Error [E0502]: 'let mut' handle is pinned
-- let ref bad_fresh = Doc.{ title: "x" } -- Error [E0543]: unanchored fresh allocation cannot bind 'let ref'

var slot = Doc.{ title: "snap1" }
slot = Doc.{ title: "snap2" }          -- OK: slot replacement of immutable snapshots
-- let ref bad_obs = slot              -- Error [E0531]: reassignable 'var' cannot anchor 'let ref'
```

### Scoped Resource Bindings

`with let [mut] x = expr` binds a non-escaping resource for the remainder of the enclosing block whose static type `T` declares an accessible `with <fn_name>` cleanup contract (`E0541` otherwise).

```ril
pub opaque type DbConn = .{ var open: bool, mut log: []str } with close

pub fn close(new c: DbConn) @Io -> () {
    let mut owned = c
    owned.open = false
    println("closed")
}

pub fn acquire() -> new DbConn {
    DbConn.{ open: true, log: [] }
}

fn run_query() @Io -> Result<int, str> {
    with let mut conn = acquire()
    conn.log |> mut Array::push("SELECT 1")
    -- close(new conn)                          -- Error [E0604]: 'with let' binding cannot be moved early
    -- with let bad_ro = acquire()              -- Error [E0541]: 'close' requires 'with let mut'
    -- with let bad_plain = 42                  -- Error [E0541]: 'int' declares no 'with' cleanup contract
    -- with var bad = acquire()                 -- Error [E0532]: 'with' resource bindings cannot use 'var'
    -- return conn                              -- Error [E0604]: 'with let' binding cannot escape block
    Ok 1                                        -- Invokes close(new conn) before returning
}
-- pub opaque type BadAsync = .{ fd: int } with async_close
-- pub fn async_close(new _c: BadAsync) @Async -> () {} -- Error [E0616]: '@Async' prohibited on 'with' cleanup
-- fn missing_io() -> () { with let mut _ = acquire() } -- Error [E0612]: unhandled @Io from close
```

| `with let` & `with <fn>` rule | Requirement |
| :--- | :--- |
| Eligible declarations (`E0541`) | `with fn_name` (attached on the same line as the type end) is permitted on `OpaqueTypeDecl`, payload-bearing `NominalDecl`, `SumTypeDecl`, and `.d.ril` `DeclOpaqueType` / payload `DeclNominalType` / `DeclSumType` (never on transparent `type A = B` or zero-payload unit `type Marker`). `fn_name` resolves in the same scope to a function returning `()` with 1 parameter of `Self` |
| Parameter mode & binding match (`E0541`, `E0527`) | `fn(new Self) [@Eff] -> ()` and `fn(mut Self) [@Eff] &mut -> ()` require `with let mut x` (satisfying `E0527` via scope-exit cleanup; under `new Self`, manual `let mut r` callers trigger `E0549` on `close(new r)`, while `with let mut r` blocks early manual `close(new r)` via `E0604`); `fn(ref Self) [@Eff] -> ()` and `fn(Self) [@Eff] -> ()` admit `with let x` (`ref Self` also admits `with let mut x` when mutated in the block, `E0527` otherwise; `.d.ril` `DeclOpaqueType` forbids plain `fn(Self)`, `E0908`). Cleanup functions must not declare `&^mut` or `&capture` (`E0541`) and must satisfy `E0910` visibility |
| Cleanup effects (`E0616`, `E0612`) | Synchronous `@Io` and user `fn` effects are permitted on `fn_name` and charged to the `with let` site (`E0612`); `@Async` suspension in a `with` cleanup contract is prohibited (`E0616: ScopedCleanupEffectError`). Enclosing `with Eff::op() -> ...` handlers declared **above** `with let` outlive it and discharge its cleanup `@Eff`; handlers declared **below** exit earlier and cannot discharge it |
| Confinement & wildcard slot (`E0532`, `E0604`) | Forbids `with var` (`E0532`), `^mut` sharing, `new x` move, return escape, and closure/fiber capture (`E0604` / `E0601`). `with let [mut] _ = expr` retains the resource in an anonymous block slot until block exit |
| Deterministic LIFO & Double-Fault | Runs once per initialized binding in reverse declaration order on block exit, `return`, `break`, `continue`, `?`, panic unwinding, and unshielded `@Async` cancellation. A secondary panic inside cleanup during active unwinding terminates the OS process immediately (bypassing `absorb_panic`) |

### Declaration Metadata Attributes

Compile-time `meta(expr1, expr2)` attributes attach deeply immutable constant values (`E0814` on non-static expressions, `E0812`/`E0816` on tokens/callables) to nominal, opaque, sum, `sub`, record-field, variant, effect, or function declarations (`E0708` on transparent `type A = B` aliases, `use`, or local `let`/`var` statements).

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

External host contracts reside in `.d.ril` files (`DeclFile`). `.d.ril` files contain declarations without bodies (`E0901` on function bodies, initializers, field defaults, `=` representation bodies on `opaque type`, or `opaque` on sum/nominal/alias declarations; standard `.ril` functions or bodyless `opaque type` declarations fail `E0902` unless matching a registered language/stdlib built-in).

```ebnf
DeclUnitItem    ::= UseDecl | DeclSub | DeclFunction | DeclType | DeclEffect | DeclLet
DeclSub         ::= { MetaAttr } [ Visibility ] "sub" PascalCase
                    "{" { DeclUnitItem Separator } [ DeclUnitItem ] "}"
DeclFunction    ::= { MetaAttr } [ Visibility ] "fn" ValueName [ GenericParams ]
                    "(" [ ParameterList ] ")" ReturnSpec [ SignatureWhereClause ]
DeclType        ::= DeclSumType | DeclNominalType | DeclTypeAlias | DeclOpaqueType
DeclTypeHead    ::= { MetaAttr } [ Visibility ] "type" PascalCase [ GenericParams ]
DeclSumType     ::= DeclTypeHead "{" VariantDeclList "}" [ WithCleanupClause ]
DeclNominalType ::= DeclTypeHead [ TypeExpression ] [ WithCleanupClause ]
DeclTypeAlias   ::= DeclTypeHead "=" TypeExpression
DeclOpaqueType  ::= { MetaAttr } [ Visibility ] "opaque" "type" PascalCase [ GenericParams ]
                    [ WithCleanupClause ]
DeclEffect      ::= { MetaAttr } [ Visibility ] "eff" PascalCase [ GenericParams ]
                    "{" [ EffectMemberList ] "}"
DeclLet         ::= [ Visibility ] "let" ScreamingSnakeCase ":" TypeExpression
```

| `.d.ril` contract rule | Requirement |
| :--- | :--- |
| Field & representation sealing (`E0907`) | Foreign opaque handles (`DeclOpaqueType`) and host-managed nominal shapes cannot be constructed directly or penetrated via field/pattern access in `.ril` (`E0907`, taking precedence over `E0308`) |
| Supported authority (`E0908`) | Foreign signatures cannot use `^mut`, `&^mut`, `&capture`, or `via`/`infer`, and cannot pass or return a `DeclOpaqueType` as an unannotated plain snapshot (`ref`, `mut`, or `new` parameter and `new` return required, `E0908`) |
| `opaque type` handles | `pub opaque type OwnedFd with close` models exclusive host-managed affine handles without mandatory-consumption viral errors: forbids `clone`, `derive`, `==`, plain `let` freezing, `^mut`, and `[M]OwnedFd` arrays (`E0301`, `E0411`); supports `new` creation/consumption (`E0549` after `new fd`), `let mut`, `mut`, `ref`, and `with let` |
| Pure `DeclLet` & `@Io` isolation (`E0906`, `E0608`) | `DeclLet` admits pure immutable value/data constants only (`DeclOpaqueType` or mutable types in `DeclLet` fail `E0906`); host-stateful foreign functions must declare `@Io` so `absorb_panic` (`E0608`) modularly isolates host side effects |

```ril
-- File: sys/posix.d.ril
pub opaque type OwnedFd with close

pub fn open_path(path: str) @Io -> new Result<OwnedFd, str>
pub fn read_bytes(ref fd: OwnedFd, max_len: int) @Io -> Result<bytes, str>
pub fn close(new fd: OwnedFd) @Io -> ()
pub sub Signals {
    pub let SIGINT: int
}
-- pub fn bad_body() -> int { 1 }          -- Error [E0901]: bodies prohibited in .d.ril
-- pub fn bad_shared(^mut fd: OwnedFd) -> () -- Error [E0908]: '^mut' unsupported on foreign contracts
-- pub fn bad_snap(fd: OwnedFd) -> ()      -- Error [E0908]: foreign opaque handle requires ref/mut/new
-- In .ril file:
-- fn unimplemented() -> int               -- Error [E0902]: body required in standard .ril module
-- let _ = fd.internal_handle              -- Error [E0907]: foreign representation is sealed
```

---

## Expressions and Operators

### Expression Grammar and Precedence

```ebnf
Expression               ::= AssignmentExpr | AnonFnExpr | AccessorExpr
AssignmentExpr           ::= AssignTarget AssignmentOperator Expression
                           | FallbackExpr
AssignTarget             ::= ValueName | MemberExpr | IndexExpr
AssignmentOperator       ::= "=" | "+=" | "-=" | "*=" | "/=" | "%="
                           | "&=" | "|=" | "^=" | "<<=" | ">>="
FallbackExpr             ::= LogicalOrExpr [ "??" FallbackExpr ]
LogicalOrExpr            ::= LogicalAndExpr { "||" LogicalAndExpr }
LogicalAndExpr           ::= ComparisonExpr { "&&" ComparisonExpr }
ComparisonExpr           ::= PipelineExpr [ RelOperator PipelineExpr ]
                           | IsExpr
RelOperator              ::= "==" | "!=" | "<" | "<=" | ">" | ">="
PipelineExpr             ::= RangeExpr { PipelineStep }
PipelineStep             ::= "|>" [ ArgumentMode ] PostfixAtomExpr [ TrailingClosure ]
                           | "as" TypeReference
ForIterable              ::= RangeExpr { "|>" [ ArgumentMode ] PostfixAtomExpr [ TrailingClosure ] }
RangeExpr                ::= BitwiseOrExpr [ ( ".." | "..=" ) BitwiseOrExpr ]
SliceRangeExpr           ::= [ BitwiseOrExpr ] ( ".." | "..=" ) [ BitwiseOrExpr ]
BitwiseOrExpr            ::= BitwiseXorExpr { "|" BitwiseXorExpr }
BitwiseXorExpr           ::= BitwiseAndExpr { "^" BitwiseAndExpr }
BitwiseAndExpr           ::= ShiftExpr { "&" ShiftExpr }
ShiftExpr                ::= AdditiveExpr { ( "<<" | ">>" ) AdditiveExpr }
AdditiveExpr             ::= MultiplicativeExpr { ( "+" | "-" ) MultiplicativeExpr }
MultiplicativeExpr       ::= UnaryExpr { ( "*" | "/" | "%" ) UnaryExpr }
UnaryExpr                ::= ( "-" | "!" | "~" ) UnaryExpr
                           | ConstructionTransferExpr
                           | SharingExpr
                           | ConstructorExpr
                           | PostfixExpr
ConstructionTransferExpr ::= "new" PostfixExpr
SharingExpr              ::= "^mut" PostfixExpr
ConstructorExpr          ::= ConstructorPath [ "new" | "^mut" ] ConstructorArg
ConstructorPath          ::= { "Super" "::" } { PascalCase "::" } PascalCase [ GenericArgs ]
ConstructorArg           ::= ( "!" | "~" ) ConstructorArg
                           | PostfixAtomExpr
PostfixExpr              ::= CallExpr | MemberExpr | IndexExpr
                           | PostfixExpr "?"
                           | AtomExpr
                           | Block
CallExpr                 ::= PostfixExpr "(" [ ArgumentList ] ")" [ TrailingClosure ]
                           | PostfixExpr TrailingClosure
TrailingClosure          ::= AnonFnExpr | AccessorExpr
ArgumentList             ::= Argument { "," Argument } [ "," ]
Argument                 ::= [ ValueName ":" ] [ ArgumentMode ] Expression
ArgumentMode             ::= "mut" | "ref" | "^mut" | "new"
TupleIndex               ::= Digit { Digit }
MemberExpr               ::= PostfixExpr ( "." | "?." ) ( FieldLabel | TupleIndex | "(" Expression ")" )
IndexExpr                ::= PostfixExpr [ "?" ] "[" ( Expression | SliceRangeExpr ) "]"
PostfixAtomExpr          ::= AtomExpr
                           | PostfixAtomExpr "(" [ ArgumentList ] ")"
                           | PostfixAtomExpr ( "." | "?." ) ( FieldLabel | TupleIndex | "(" Expression ")" )
                           | PostfixAtomExpr [ "?" ] "[" ( Expression | SliceRangeExpr ) "]"
                           | PostfixAtomExpr "?"
AtomExpr                 ::= Literal
                           | HoleExpr
                           | QualifiedName [ GenericArgs ]
                           | RecordExpr
                           | TupleExpr
                           | ArrayExpr
                           | MapExpr
                           | TypeQuoteExpr
                           | IfExpr | MatchExpr | WhileExpr | ForExpr
                           | "(" Expression ")"
HoleExpr                 ::= "..."
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
| 1 | `.` `?.` `f(...)` `f \...` `a[i]` `a?[i]` `?` `Type.{...}` `::` | Left |
| 2 | Unary `-` `!` `~` `typeof` `^mut e` `new e`, space constructor `Tag arg` | Right |
| 3 | `*` `/` `%` | Left |
| 4 | `+` `-` | Left |
| 5 | `<<` `>>` | Left |
| 6 | `&` | Left |
| 7 | `^` | Left |
| 8 | `\|` | Left |
| 9 | `..` `..=` | Non-associative |
| 10 | `\|>` `\|> ref` `\|> mut` `\|> ^mut` `\|> new`, `e as SupType` | Left |
| 11 | `==` `!=` `<` `<=` `>` `>=` `is` | Non-associative |
| 12 | `&&` | Left (short-circuit) |
| 13 | `\|\|` | Left (short-circuit) |
| 14 | `??` | Right (short-circuit) |
| 15 | `let ... else` | Non-associative |
| 16 | `=` `+=` `-=` `*=` `/=` `%=` `&=` `\|=` `^=` `<<=` `>>=` | Non-associative (`E0701`) |
| 17 | `where` (`BlockWhereClause`) | Non-associative |

- **Lexical Adjacency vs. Space Construction (`E0125`)**: Function calls attach `(` (`parse(s)`), array/map indexing attaches `[` (`xs[0]`), and all named record constructions attach `.{` (`User.{ id: 1 }`). Sum variants and non-record nominal constructors require whitespace before their payload (`Ok 42`, `Ok ()`, `Some .{ x: 1 }`, `Some [1, 2]`, `Ok (-1)`). Bare `Block` `{...}` and bare `AnonFnExpr` `\...` are excluded from `ConstructorArg`, so `if opt == None { ... }` and `call(None) \-> ...` parse unambiguously.
- **Expression Holes (`...`, `E0360`)**: `...` has type `never`, satisfies any expected type and access mode during partial checking, and suppresses cascading `E0527` / `E0549` diagnostics along paths ending in `...`, while failing complete builds with `E0360: UnfinishedExpressionHoleError`.

```ril
type Buf = .{ var len: int }
-- fn draft_fill(mut buf: Buf) &mut -> int {
--     ...                                -- Error [E0360]: unfinished expression hole in complete build
-- }
```

### Arithmetic, Bitwise, Relational, and Logical Operators

- **Arithmetic (`+`, `-`, `*`, `/`, `%`, unary `-`)**: Defined exclusively on `(int, int) -> int` and `(f64, f64) -> f64` (`E0327` on `str`, `bytes`, or `bool`; strings combine via interpolation `"{a}{b}"`). Integer `/` truncates toward zero and `%` satisfies `(a / b) * b + (a % b) == a`. Constant integer division/remainder by `0` fails `E0361`; dynamic `/ 0` or `% 0` panics (`Numeric::checked_div` and `Numeric::checked_rem` return `?int` without panicking). Explicit numeric conversions use `Numeric::to_f64(n: int) -> f64`, `Numeric::convert<int>(x: f64) -> ?int`, and `Numeric::trunc(x: f64) -> ?int`.
- **Bitwise & Shifts (`~`, `&`, `|`, `^`, `<<`, `>>`)**: Defined exclusively on `int` (`E0327` elsewhere) using infinite-width two's-complement semantics (`~x == -x - 1`, `x >> k` arithmetic floor shift). Constant negative shift count `k < 0` fails `E0361`; dynamic `k < 0` panics.
- **Equality & Ordering (`==`, `!=`, `<`, `<=`, `>`, `>=`)**:
  - `==` / `!=` require same-type operands (`E0301`, `E0305` on distinct nominals) whose type recursively excludes callables, `.d.ril` `opaque` handles, `Scope`, `Task`, `Sender`, `Receiver`, and `Draft` (`E0327`; `f64` follows IEEE-754 where `NaN != NaN` and `-0.0 == 0.0`, and `?T == None` / `!= None` tests the option tag even when `T` lacks equality). Map keys and `Set` elements additionally forbid `f64`, extensible `{ .. }` sums, and mutable member modes (`E0328`).
  - `<`, `<=`, `>`, `>=` apply to same-type `int`, `f64`, `str` (lexicographic UTF-8 scalar order), and `bytes` (`E0327` elsewhere).
- **Logical (`!`, `&&`, `||`)**: Require `bool` operands (`E0350`); `&&` and `||` short-circuit left-to-right.

```ril
assert(7 / 3 == 2 && -7 / 3 == -2 && -7 % 3 == -1)
assert((~0 == -1) && ((-8 >> 2) == -2) && ((1 << 100) > 0))
-- let bad_str_add = "a" + "b"          -- Error [E0327]: '+' is numeric only; write '"{a}{b}"'
-- let bad_div = 10 / 0                 -- Error [E0361]: constant zero divisor
-- let bad_shl = 1 << -3                -- Error [E0361]: constant negative shift count
-- let bad_bit = true & false           -- Error [E0327]: bitwise '&' requires 'int'
```

#### Value Tests with is

`expr is IsTest` performs asymmetric, non-binding pattern testing of variant tags, subset sums, record subsets, tuples, string slices, integer ranges, and existing leaf values/expressions, returning `bool` with left-to-right structural short-circuiting and driving [flow-sensitive type narrowing](#flow-sensitive-type-narrowing).

```ebnf
IsExpr           ::= PipelineExpr "is" IsTest
IsTest           ::= IsAlternative { "|" IsAlternative }
IsAlternative    ::= "_"
                   | IsSumSubset
                   | IsConstructor
                   | IsTuple
                   | IsRecord
                   | IsStr
                   | RangePattern
                   | IsValueExpr
IsSumSubset      ::= ".." TypeReference
IsConstructor    ::= ConstructorPath [ IsConstructorArg ]
IsConstructorArg ::= "_"
                   | IsTuple
                   | IsRecord
                   | IsStr
                   | "(" IsTest ")"
                   | PostfixAtomExpr
IsTuple          ::= "(" ")" | "(" IsTest "," IsTest { "," IsTest } [ "," ] ")"
IsRecord         ::= [ TypeReference ] ".{" [ IsField { "," IsField } [ "," ] ] "}"
IsField          ::= FieldLabel [ ":" IsTest ]
IsStr            ::= "str[" [ IsStrItem { "," IsStrItem } [ "," ] ] "]"
IsStrItem        ::= ".." | Expression
IsValueExpr      ::= BitwiseXorExpr
```

| `is` form | Semantics & static checks |
| :--- | :--- |
| `e is Tag` / `e is Tag _` | Tests sum/nominal constructor tag without requiring payload equality (`E0125` on tight `Tag(_)`) |
| `e is Tag subtest` | Tests tag first; only on match evaluates/tests payload (`Ok 42`, `Ok wanted`, `Ok (expected())`, `Item (a, b)`, `Some .{ id: 1 }`) |
| `e is ..SubType` | Succeeds when `e`'s tag belongs to closed transparent `SubType` with $SubType \preceq_{\text{sum}} Sup$ (`E0301`/`E0306`/`E0308`) |
| `e is .{ f1: t1, f2 }` | Tests listed known fields in written order (`f2` reads outer variable `f2` and compares `e.f2 == f2`); omitted fields are unconstrained |
| `e is str[p, .., s]` | Tests dynamic or literal `str` prefix/suffix chunks with at most one `..` (`E0347` on duplicate `..`, `E0349` on multiple items after `..`) |
| `e is a \| b` vs `e is (a \| b)` | Top-level `\|` separates test alternatives; parenthesized `(a \| b)` evaluates bitwise OR and compares with `==` |
| Non-binding (`E0204`, `E0120`) | Leaves read existing names or evaluate expressions (`E0204` on unbound names; `E0120` on `mut`/`ref` modifiers or trailing `if`) |

```ril
fn expected() -> int { 42 }
let wanted = 42
let answer: Result<int, str> = Ok 42
assert(answer is Ok && answer is Ok _ && answer is Ok wanted && answer is Ok (expected()))

let failed: Result<int, str> = Err "boom"
assert(!(failed is Ok (panic("skipped"))))      -- Tag mismatch skips leaf evaluation

let dir = "src/"
let path = "src/lexer.ril"
assert(path is str[dir, .., ".ril"])
assert(3 is 1 | 3 && 3 is (1 | 2))
-- let _ = answer is Ok unknown_var             -- Error [E0204]: 'is' never binds new names
-- let _ = answer is Ok(42)                     -- Error [E0125]: space required after constructor 'Ok'
```

### Indexing, Slicing, and Static Coordinate Projection

- **Indexing & Slicing (`xs[i]`, `xs?[i]`, `xs[a..b]`, `xs[a..=b]`)**:
  - Arrays `[M]T` accept `int` element indices (`xs[i]` panics out of bounds; `xs?[i] -> ?T` returns `None` out of bounds). Single-element bracket indexing on `str` or `bytes` is rejected (`E0352`; use `String::at` / `Bytes::at`), and dynamic bracket indexing on records fails `E0324`.
  - Sequence slicing `s[a..b]` / `s[a..=b]` (and safe `s?[a..b]`) produces a fresh array on `[M]T` (preserving element modes; binding directly to `let ref` fails `E0543`), a Unicode-scalar sub-string on `str`, and a byte sub-sequence on `bytes`.
  - Maps `[K: M V]` require safe lookup `m?[k] -> ?V` for reads (`E0352` on `m[k]` reads or `m[k] += v`); direct slot assignment `m[k] = v` inserts or updates key `k`. Mutating a live array/map while holding a `ref` element projection or during `for` iteration over it fails `E0537` / `E0526`.
- **Tuple & Static Coordinate Projection (`t.0`, `r.(key)`)**: `t.0` projects tuple elements or narrowed single/tuple variant payloads (`E0312` out of bounds; `E0337` on unnarrowed sums, collections, or primitives); `r.(key)` projects a record field or tuple slot using a compile-time `meta` coordinate `key` validated by `Key<T>`.

```ril
let xs = [10, 20, 30, 40]
let text = "hello, 世界"
assert(xs[1..3] == [20, 30] && xs?[9] == None && text[0..5] == "hello")
let m = ["port": 8080]
assert(m?["port"] == Some 8080 && m?["host"] == None)
-- let _ = m["port"]                    -- Error [E0352]: map read requires 'm?["port"]'
-- let _ = "abc"[0]                     -- Error [E0352]: 'str' element access uses 'String::at'
-- let _ = (Some 1).0                   -- Error [E0337]: unnarrowed sum has no '.0' projection
type Cell = .{ var v: int }
let mut cells = [Cell.{ v: 1 }]
let ref elem = cells[0]
-- cells |> mut Array::push(Cell.{ v: 2 }) -- Error [E0537]: mutating array while 'elem' is live
assert(elem.v == 1)
cells |> mut Array::push(Cell.{ v: 2 }) -- OK: 'elem' last use has ended
```

### Text and Byte Operations

Strings combine via interpolation `"{left}{right}"` or `String::join`. Prelude modules `String` and `Bytes` provide dual-phase UTF-8 and byte conversions:
- `String::at(text: str, index: int) -> ?int`, `String::scalars(text: str) -> new []int`, `String::from_scalars(via values: []int) -> ?str`
- `String::encode_utf8(text: str) -> bytes`, `String::decode_utf8(data: bytes) -> ?str` (`None` on ill-formed UTF-8)
- `Bytes::at(data: bytes, index: int) -> ?int`, `Bytes::to_array(data: bytes) -> new []int`, `Bytes::from_array(via values: []int) -> ?bytes` (`None` if any integer lies outside `0..=255`)

```ril
assert(Bytes::from_array([65, 66]) == Some bytes"AB" && Bytes::from_array([256]) == None)
assert(String::decode_utf8(String::encode_utf8("Ril")) == Some "Ril")
assert(String::decode_utf8(bytes"\xC0\xAF") == None)
```

### Pipeline and Fallible Operators

- **Mode-Aware Pipelines (`x |> [mode] f(a)` / `x |> [mode] f`)**: Evaluates `x` first, then callee `f` and remaining arguments left-to-right, passing `x` as the first argument under `[mode]` (`E0338` if `f` is non-callable):

| Pipeline form | Equivalent call | Left-operand requirement |
| :--- | :--- | :--- |
| `x \|> f` / `x \|> f(a)` | `f(x)` / `f(x, a)` | `Expression` (immutable snapshot, value copy, or lexical `via`) |
| `x \|> ref f` / `x \|> ref f(a)` | `f(ref x)` / `f(ref x, a)` | `Expression` (scoped read-only `ref` borrow) |
| `x \|> mut f` / `x \|> mut f(a)` | `f(mut x)` / `f(mut x, a)` | `AssignTarget` (`E0410` on non-place rvalues) |
| `x \|> ^mut f` / `x \|> ^mut f(a)` | `f(^mut x)` / `f(^mut x, a)` | `AssignTarget` (`E0410` on non-place rvalues) |
| `x \|> new f` / `x \|> new f(a)` | `f(new x)` / `f(new x, a)` | `Expression` (ends `x` before evaluating `f` or `a`, `E0549`) |

- **Error/Option Propagation (`expr?`)**: Valid inside an ordinary function or closure body (`E0205` at module/`sub` top-level); preserves `new` construction qualification on the unwrapped `Ok`/`Some` payload:
  - On `Result<T, E>` (`E0712` on non-`Result`/non-`Option`): unwraps `Ok v` to `v`, or early-returns `Err e` (widening `e` when $E \preceq_{\text{sum}} E_{\text{ret}}$; incompatible enclosing return types fail `E0713`).
  - On `?T`: unwraps `Some v` to `v`, or early-returns `None` when the enclosing callable returns `?U` (`E0713` otherwise).
- **Right-Associative Fallback (`opt ?? b ?? c` / `res ?? \err -> fallback`)**:
  - `?T ?? T`: evaluates right operand lazily only on `None` (`E0714` on invalid left operand).
  - `Result<T, E> ?? fn(E) @... -> T`: invokes the handler closure with `e` on `Err e`, discharging `Result`'s `E0720` obligation (`E0711` if right operand is not `fn(E) -> T`; outer `break`/`continue`/`return` across a fallback or closure boundary fails `E0707`/`E0710`).
- **Safe Navigation (`opt?.field`, `opt?[idx]`)**: `?.` requires `?T` receiver (`E0715` otherwise), short-circuiting `None` to `None` and lifting `U` to `?U` without double-wrapping existing `?U`.

```ril
type Config = .{ host: ?str }
fn resolve_host(cfg: ?Config) -> str { cfg?.host ?? "localhost" }

let mut buf = [1, 2]
buf |> mut Array::push(3)
assert(buf |> ref len == 3 && resolve_host(None) == "localhost")
-- clone(ref buf) |> mut Array::push(4) -- Error [E0410]: '|> mut' requires an AssignTarget
-- let top_q = (Ok 1)?                  -- Error [E0205]: '?' outside function/closure frame
-- let _ = 1 |> 2                       -- Error [E0338]: pipeline target is not callable
-- let _ = 42?                          -- Error [E0712]: '?' requires Result or Option
-- fn bad_prop() -> int { (None)? }     -- Error [E0713]: enclosing return type is not Option
-- let _ = 42 ?? 0                      -- Error [E0714]: '??' requires Option or Result
-- let _ = (Ok 1) ?? 0                  -- Error [E0711]: Result '??' requires error handler 'fn(E) -> T'
-- let _ = 42?.host                     -- Error [E0715]: '?.' requires optional '?T' receiver
-- fn bad_fb(o: ?int) -> int { o ?? return 0 } -- Error [E0710]: control transfer inside '??' fallback
```

### Record Construction and Assignments

- **Record Construction (`[Type].{ field: expr, shorthand }`)**: Must initialize every non-defaulted declared field of the target record type (`E0307` missing, `E0302` unexpected, `E0210` duplicate). Field punning `.{ id, name }` desugars to `.{ id: id, name: name }`.
- **Assignments (`target = expr`, `target += expr`, ...)**: Assignment is a `()`-typed expression and does not chain (`a = b = 1` fails `E0701`). `target` must be a `var` variable, a `var` record field on a `mut`/`^mut` path, or an element of a `mut`/`^mut` array/map (`E0501` on `let`, `E0502` on pinned `let mut`/`let ref`, `E0503` on rvalues; map compound assignment `m[k] += v` fails `E0352`). Compound assignments evaluate `target`'s receiver/index expression exactly once.

```ril
var a = 1
var b = 2
a += b
b += 1
assert(a == 3 && b == 3)
-- 10 = 20                             -- Error [E0503]: invalid assignment target
-- a = b = 3                           -- Error [E0701]: chained assignment is prohibited
```

---

## Control Flow and Pattern Matching

### Block Expressions and Local Declarations

```ebnf
Block             ::= "{" [ StatementSequence ] [ BlockWhereClause ] "}"
StatementSequence ::= Statement { Separator Statement } [ Separator ]
Statement         ::= UseDecl
                    | MetaLetDecl
                    | LetDecl | LetMutDecl | SharedMutDecl
                    | VarDecl | VarMutDecl | LetRefDecl | VarRefDecl
                    | ModePreservingBinding | WithLetDecl
                    | GuardedLetStmt
                    | WithStatement
                    | ControlTransfer
                    | Expression
BlockWhereClause  ::= "where" BlockWhereItem { Separator BlockWhereItem } [ Separator ]
BlockWhereItem    ::= FunctionDecl | LocalTypeDecl | EffectDecl | MetaFnDecl
Separator         ::= ";" | Newline
```

- **Value of a Block**: A block evaluates `StatementSequence` top-to-bottom; its value is the trailing `Expression` if not followed by `;`, or `()` otherwise.
- **Hoisted `BlockWhereClause` (`E0702`, `E0703`, `E0207`, `E0315`, `E0618`)**:
  - Local `fn`, `meta fn`, `type`, and `eff` declarations inside a block must be placed in the block's trailing `where` clause; placing them in `StatementSequence` fails `E0703: IllegalSequentialDeclarationError`, and placing value bindings (`let`, `var`), `sub`, or statements inside `BlockWhereClause` fails `E0702: InvalidWhereItemError`.
  - All declarations in `BlockWhereClause` form one mutually recursive scope hoisted across the entire enclosing block. Value bindings (`let`, `var`, `with let`) enter scope strictly after their initializer completes; invoking a `where` helper before an outer local variable it captures has been initialized fails `E0207`.
  - Block-local nominal/opaque/sum types cannot escape in the enclosing callable's return type or outer mutable storage (`E0315`). Block-local `eff` effects must be handled inside their declaring block (`E0618`). Visibility modifiers (`pub`, `pub(pkg)`) are prohibited inside blocks (`E0703` / `E0120`).

```ril
fn compute_tree() -> int {
    -- let bad_self = bad_self + 1     -- Error [E0207]: 'bad_self' used before initialization
    -- fn seq_fn() -> int { 1 }        -- Error [E0703]: move local 'fn' to trailing 'where' clause
    -- let early = sum(Leaf 1)         -- Error [E0207]: 'sum' captures 'base' before 'base' is initialized
    let base = 10
    sum(Node (Leaf 1, Leaf 2))         -- Returning 'Leaf 1' from 'compute_tree' would fail E0315
where
    type Tree { Leaf int, Node (Tree, Tree) }
    fn sum(t: Tree) &up{base} -> int {
        match t {
            Leaf v      -> v + base,
            Node (l, r) -> sum(l) + sum(r),
        }
    }
    -- let bad_where_let = 1           -- Error [E0702]: value bindings are prohibited in 'where'
    -- eff EscEff { fn ping() -> () }  -- Unhandled EscEff::ping() in block fails E0618
}
assert(compute_tree() == 23)
```

### Conditional and Loop Expressions

```ebnf
IfExpr          ::= "if" ( Expression | "let" Pattern "=" Expression ) Block
                    [ "else" ( IfExpr | Block ) ]
WhileExpr       ::= "while" ( Expression | "let" Pattern "=" Expression ) Block
ForExpr         ::= "for" ForIterable "as" Pattern Block
ControlTransfer ::= "return" [ Expression ]
                  | "break"
                  | "continue"
```

- **Conditionals**: `if cond { a } else { b }` requires `cond: bool` (`E0350`) and a common join type across normal branches (`E0351`). Without `else`, the `then` block must have type `()` (or `never`). `if let pat = expr { ... } [else { ... }]` matches refutable `pat` against `expr`.
- **Loops & Transfers (`E0355`, `E0707`)**:
  - `while cond { body }` (`cond: bool`, `E0350`) and `while let pat = expr { body }` check `body` against `()`. When `cond` is syntactically the bare boolean literal `true` (`while true { ... }`) and `body` contains no `break` targeting that `while` (ignoring `break`s captured by nested inner loops), the expression has no normal continuation and synthesizes `never`; all other `while` expressions synthesize `()`.
  - `for iter as pat { body }` iterates over `[]T`, `[K: V]` (yielding `(K, V)`), `Set<T>`, or integer ranges `a..b` / `a..=b` (`E0355` on non-iterable values), checking `body` against `()` and synthesizing `()`. `pat` must be irrefutable (`E0345`).
  - `break` and `continue` target the innermost enclosing `while` or `for` in the same callable (`E0707` outside a loop or across a closure boundary). `return` exits the innermost enclosing `fn` or `\... ->` closure (`return` ≡ `return ()`).

```ril
fn find_odd_sum() -> int {
    var acc = 0
    for 1..=10 as i {
        if i % 2 == 0 { continue }
        if i > 7 { break }
        acc += i
    }
    while true {
        return acc                         -- 'while true' with no targeting 'break' synthesizes 'never'
    }
}
assert(find_odd_sum() == 16)
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

Plain `let Pat = expr` without `else` requires an irrefutable pattern (`E0345`) that introduces at least one variable binder (except explicit `let _ = expr`; vacuous `let () = f()` or `let Marker = m` fails `E0309`).

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
SubsetPattern        ::= TypeReference "as" ( [ BindingModifier ] ValueName | Wildcard )
                       | ".." TypeReference
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
                       | ByteStringLiteral | "true" | "false"
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

### Flow-Sensitive Type Narrowing

Conditions using `is`, `== None`, `!= None`, `!`, `&&`, `||`, and early-diverging `if` / `while` guards refine the static type of existing bindings and field paths in-place across dominance regions without introducing new variable names:

| Narrowing rule | Requirement |
| :--- | :--- |
| Optional unboxing | `x != None` (or `!(x == None)`) narrows `x: ?T` directly to `T`; `if x == None { return ... }` narrows sequential successor flow to `T` |
| Sum projection ($S\|_V$, `E0337`) | Narrowing sum `x: S` to a single variant $V$ (with no active open `..` residual) enables direct payload access: `x.field` for record payload `V .{...}`, `x.0` / `x.1` for tuple payload `V (A, B)`, `x.0` for single non-unit/non-record/non-tuple payload `V T`, and no projection for unit `V` or `V ()` (`E0337` when multiple variants remain active or `V` is unit/`()`) |
| Negative exclusion & `..Sub` | Failing `x is V` or `x is V _` excludes `V` from the `else` branch; failing `x is V expected_val` does **not** exclude `V` because the tag may still be `V` with a different payload. `x is ..Sub` narrows to `Sub` on true and excludes `Sub` on false |
| Contradictory test (`E0311`) | A narrowing predicate disjoint from all remaining active variants of the narrowed target fails `E0311: ContradictoryNarrowingError` |
| Write invalidation (`E0310`) | Immutable `let` paths through immutable fields narrow across dominance regions without depth limit. Reassigning a `var` slot or performing a known write/call reaching a narrowed mutable field resets that refinement; subsequent narrowed access fails `E0310: InvalidatedNarrowingAccessError` |
| Unknown alias hazard (`E0533`) | Across an open-state callback (`fn() & -> ()`) or call whose write independence from a live-origin path cannot be proved (`ref` does not prove independence; `clone` into a plain `let` snapshot does), accessing the prior live refinement fails `E0533: AliasedNarrowingHazardError` |

```ril
type Geometry { Circle f64, Rect (f64, f64), Click .{ x: int }, Point }
type Cell = .{ var val: ?int }

fn area(g: Geometry) -> f64 {
    if g is Circle {
        -- if g is Rect { return 0.0 }          -- Error [E0311]: contradictory narrowing ('g' is already 'Circle')
        3.14159 * g.0 * g.0                     -- Single payload projected via '.0'
    } else if g is Rect {
        g.0 * g.1                               -- Tuple payload projected via '.0', '.1'
    } else if g is Click {
        Numeric::to_f64(g.x)                    -- Record payload projected via '.x'
    } else {
        0.0                                     -- 'Point' remains
    }
}

fn check_hazards(mut cell: Cell, hook: fn() & -> ()) &mut -> int {
    var local: ?int = Some 10
    if local != None {
        let ok = local + 1
        local = None
        -- let _ = local + 1                    -- Error [E0310]: 'local' narrowing invalidated by assignment
        let _ = ok
    }
    if cell.val != None {
        hook()
        -- let _ = cell.val + 1                 -- Error [E0533]: unproved callback overlap with live 'cell.val'
    }
    let snap = clone(ref cell)
    cell.val = None
    if snap.val != None { snap.val } else { 0 } -- OK: immutable 'snap' survives 'hook()' and 'cell' writes
}
assert(area(Rect (3.0, 4.0)) == 12.0)
```

---

## Functions, Closures, and Callables

### Named Function Declarations and Contrast Matrix

```ebnf
FunctionDecl         ::= { MetaAttr } [ Visibility ] "fn" ValueName [ GenericParams ]
                         "(" [ ParameterList ] ")" ReturnSpec
                         [ SignatureWhereClause ] [ Block ]
SignatureWhereClause ::= "where" ( "{" SignatureWhereList "}" | SignatureWhereList )
SignatureWhereList   ::= SignatureWhereItem { Separator SignatureWhereItem } [ Separator ]
SignatureWhereItem   ::= LocalTypeDecl | FunctionDecl | MetaFnDecl
ParameterList        ::= Parameter { "," Parameter } [ "," ]
Parameter            ::= RegularParam | MetaParam
RegularParam         ::= [ ParameterMode ] ( ValueName | Wildcard )
                         ( ":" TypeExpression { ContractGuard } | ContractGuard { ContractGuard } )
                         [ "=" Expression ]
MetaParam            ::= "meta" ( ValueName | Wildcard ) [ ":" TypeExpression ]
                         { "|>" PipelineConstraint } [ "=" Expression ]
ParameterMode        ::= "mut" | "^mut" | "ref" | "new" | "via"
ReturnSpec           ::= [ EffectAnnot ] [ StateAnnot ] "->" ReturnType { ContractGuard }
ContractGuard        ::= "|>" [ "ref" ] QualifiedName [ GenericArgs ] [ "(" [ ContractArgList ] ")" ]
ContractArgList      ::= ContractArg { "," ContractArg } [ "," ]
ContractArg          ::= [ ValueName ":" ] ( [ "ref" ] QualifiedName | [ "-" ] Literal )
ReturnType           ::= [ ReturnMode ] TypeExpression
ReturnMode           ::= "new"
                       | "infer"
                       | ( "ref" | "^mut" ) "(" ReturnSources ")"
ReturnSources        ::= ValueName { "|" ValueName }
```

| Declaration kind | Syntax | Phase | Effects & state |
| :--- | :--- | :--- | :--- |
| Ordinary `fn` | `fn f(...) [@Eff] [&State] -> T { ... }` | Run-time (`len`/`panic`/`assert` dual-phase) | Explicit `@Eff` and minimal `&State` required on named definitions (`E0510`, `E0529`, `E0612`) |
| Compile-time `meta fn` | `meta fn f(...) -> T { ... }` | Static (`TypeEval` / `MetaValue` + saturated compile-time fold in `RunTime`) | Pure only (`E0813`); result token-free (`E0812`) |
| Type function | `type F = \T -> <...>` | Static (`TypeEval`) | Pure only (`E0335`); returns single `Type<U>` token |
| Built-in bodyless `fn` | Bodyless `fn` in prelude `.ril` | Per primitive contract | Must match registered primitive module, name, and signature (`E0902`, `E0909`) |
| Foreign `.d.ril` `fn` | Bodyless `pub fn` in `.d.ril` | Run-time | Body prohibited (`E0901`); stateful host calls declare `@Io` |

#### Dual-Tier Where Invariants

| Tier rule | Requirement |
| :--- | :--- |
| `SignatureWhereClause` (`E0704`) | Admits `LocalTypeDecl` (`type`), `FunctionDecl` (`fn`), and `MetaFnDecl` (`meta fn`); declaring `eff` or `sub` fails `E0704: InvalidSignatureWhereItemError` (value bindings fail `E0702`). Visible across the function signature (`PipelineConstraint`s, `ContractGuard`s, types) and body |
| Signature confinement (`E0706`) | Types and guards referenced in the signature must be declared in `SignatureWhereClause` or an enclosing scope; referencing `BlockWhereClause` items in the signature fails `E0706: SignatureTypeNotInSignatureWhereError` |
| Downward isolation & uniqueness (`E0705`, `E0203`) | `SignatureWhereClause` items cannot reference `BlockWhereClause` items (`E0705: DownwardScopeReferenceError`), whereas `BlockWhereClause` may reference `SignatureWhereClause`. Duplicate names across both tiers fail `E0203` |

```ril
pub fn map_fallible<T, R, E>(xs: []T, step: StepFn<T, R, E>) @Io -> Result<[]R, E>
where
    type StepFn<In, Out, Err> = fn(In) @Io -> Result<Out, Err>
{
    let mut out: []R = []
    for xs as item { Array::push(mut out, step(item)?) }
    Ok out
where
    fn _helper_tag() -> int { 1 }
}

-- fn bad_sig_eff(x: int) -> int where eff E { fn op() -> () } { x } -- Error [E0704]: 'eff' prohibited in signature 'where'
-- fn bad_down() -> Wrap where type Wrap = .{ s: Inner } { Wrap.{ s: .{ n: 0 } } where type Inner = .{ n: int } } -- Error [E0705]
-- fn bad_sig_ref(cb: Cb) -> () { cb() where type Cb = fn() -> () }  -- Error [E0706]: signature references block 'where'
```

#### Signature Value Contracts

`ContractGuard` (`|> [ref] guard(args)`) attaches declarative fallible entry and exit contracts to `RegularParam` and declaration `ReturnSpec` (`FunctionDecl`, `MetaFnDecl`, `DeclFunction`):

| Contract rule | Requirement |
| :--- | :--- |
| Parameter type omission (`E0544`) | A `RegularParam` with at least one `ContractGuard` may omit `: TypeExpression`, inferring its type from the first guard's leading parameter (`E0544` if both `: Type` and guards are omitted; `E0344` if undetermined) |
| Pure fallible guard (`E0409`, `E0712`, `E0713`) | Guards must be pure (`E0409` on `@Eff` or mutable/capturing state) and return `Result<(), E>` or `?()` (`E0712`) compatible under `?` with the enclosing function's `Result<T, E_out>` or `?T` return type (`E0713`) |
| Evaluation & `|> ref` (`E0549`, `E0527`) | Arguments and defaults bind left-to-right first; parameter guards then run in declaration order via `(p |> [ref] guard(args))?`. On `Ok v` / `Some v` return (`Err` / `None` bypasses exit guards), return guards run via `(v |> [ref] guard(args))?`. `|> ref` preserves `new` qualification on `v`; reading a consumed `new` parameter in a return guard fails `E0549`, and guards alone do not satisfy `E0527` |

```ril
pub type Span = .{ lo: int, hi: int }
pub type SpanErr { Inverted, Empty }

pub fn make_span(lo |> ordered(hi), hi: int) -> Result<Span, SpanErr> |> non_empty
where
    fn ordered(lo: int, hi: int) -> Result<(), SpanErr> {
        if lo <= hi { Ok () } else { Err SpanErr::Inverted }
    }
    fn non_empty(s: Span) -> Result<(), SpanErr> {
        if s.hi > s.lo { Ok () } else { Err SpanErr::Empty }
    }
{
    Ok Span.{ lo, hi }
}

fn test_contracts() -> () {
    assert(make_span(2, 5) == Ok Span.{ lo: 2, hi: 5 })
    assert(make_span(5, 2) == Err SpanErr::Inverted)
    assert(make_span(3, 3) == Err SpanErr::Empty)
}
test_contracts()
-- fn bad_bool_guard(x: int |> pos) -> ?int where fn pos(n: int) -> bool { n > 0 } { Some x } -- Error [E0712]
-- fn bad_ret_guard(x: int |> pos) -> int where fn pos(n: int) -> ?() { Some () } { x }       -- Error [E0713]
-- fn bad_untyped(x) -> ?int { Some x }                                                       -- Error [E0544]
```

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
- Named `fn` declarations must spell exact unhandled operational `@Eff` (`E0612`), minimal concrete state obligations (`&mut`, `&^mut`, `&capture`, `&up{...}`, `&return{...}` — `E0510` when missing, `E0529` when excessive), and non-plain return modes (`new`, `ref(x)`, `^mut(x)` — `E0544` / `E0528`), except where `via` / `infer` encapsulates mode-dependent obligations.
- Anonymous closures `\... -> ...` infer their exact contract automatically; optional written `@Eff` / `&State` / `: Type` annotations constrain inference.

#### Closed and Open Callable Rows

| Callable annotation | Operational effects | State & provenance |
| :--- | :--- | :--- |
| *(omitted)* | Closed empty (`@{}`) | Closed pure (`&{}`) |
| `@Io` | Closed `{Io}` | Closed pure (`&{}`) |
| `&up` | Closed empty (`@{}`) | Abstract captured closure environment |
| `@` | Open effect row | Closed pure (`&{}`) |
| `&` | Closed empty (`@{}`) | Open state/provenance row |
| `@&` | Open effect row | Open state/provenance row |

Open markers `@`, `&`, and `@&` are valid only on `CallableType` parameters/fields (`E0547` on named or anonymous definitions).

#### Callable Contract Matching

Under `MatchCallable`, a callable value of actual contract $C_{\text{act}}$ satisfies expected `CallableType` $C_{\text{exp}}$ (`E0534` on mismatch, `E0407` on parameter mode mismatch) iff:
1. Parameter count matches (`E0314`), parameter types satisfy contravariance, return type satisfies covariance, and concrete parameter/return access modes match (`E0407`; `mut` and `^mut` definitions still satisfy `E0527`).
2. Every operational effect in $C_{\text{act}}$ appears in $C_{\text{exp}}$ (unless $C_{\text{exp}}$ is effect-open via `@` or `@&`).
3. Every non-pure state/capture obligation in $C_{\text{act}}$ is permitted by $C_{\text{exp}}$ (`&up` admits observer/capturing closure environments; mutable closure environments require caller-side `mut` / `^mut` handle invocation; `&` / `@&` opens state obligations). Pure module constants, pure immutable captures, and pure stateless lexical `fn` handlers reduce to empty state `&{}`.

```ril
-- pub fn len(x: int) -> int            -- Error [E0909]: built-in signature mismatch in prelude
-- fn bad_open() @ -> () {}             -- Error [E0547]: open '@' row prohibited on named 'fn'
-- fn bad_ret(ref a: []int) -> []int { a } -- Error [E0544]: missing 'ref(a)' return mode annotation
-- let pure_cb: fn() -> () = \-> println("hi")         -- Error [E0534]: '@Io' incompatible with pure 'fn() -> ()'
-- let mode_cb: fn([]int) -> () = \mut xs: []int -> Array::push(mut xs, 1) -- Error [E0407]: mode 'mut' vs plain
-- let idle_cb = \mut _xs: []int -> ()                 -- Error [E0527]: wildcard does not waive 'mut' use
```

### Return Construction, Access Modes, and Sources

| Return form | Meaning & static check |
| :--- | :--- |
| `-> T` | Deeply immutable snapshot or value copy (`E0528` / `E0535` if live or writable) |
| `-> new T` | Completely newly constructed or `new`-transferred isolated graph free of external object aliases (`E0546` otherwise); the receiving binding or parameter determines its concrete shape (`let xs: []U`, `let mut xs: []U`, `let mut xs: [mut]U`, `let mut xs: [^mut]U`) |
| `-> ref(x \| y) T` | Read-only view rooted in formal `x` or `y`'s call-entry graph (`E0545` if rooted in a local or borrowed sum-subset wrapper) |
| `-> ^mut(x) T` | Shared writable handle rooted in `^mut x`'s call-entry graph (`E0545` if `x` is temporary `mut`; root retention needs no duplicate `&^mut`, `E0529`) |
| `&return{ref x, ^mut y}` | Records contained live/shared origins inside a composite return value |

```ril
type Node = .{ var val: int }

fn pick_ref(cond: bool, ref a: Node, ref b: Node) -> ref(a | b) Node {
    if cond { a } else { b }
}

fn make_nodes() -> new []Node {
    [Node.{ val: 1 }, Node.{ val: 2 }]
}

fn test_returns() -> () {
    let snap: []Node = make_nodes()            -- Receiver freezes graph as immutable []Node
    let mut edit: [mut]Node = make_nodes()     -- Receiver adopts fresh graph as [mut]Node
    edit[0].val = 10
    assert(snap[0].val == 1 && edit[0].val == 10)
}
test_returns()
-- fn bad_wrap(n: Node) -> new []Node { [n] }    -- Error [E0546]: embeds aliased 'n' in 'new' graph
-- fn bad_src(mut a: Node) &mut -> ^mut(a) Node { a.val += 1; a } -- Error [E0545] / [E0528]
-- fn bad_new(ref a: Node) -> new Node { a }     -- Error [E0546]: 'ref' is not fresh 'new'
```

### Parameter Modes, Caller Obligations, and Defaults

Parameters forbid `var` (`E0403`; copy into a local `var` if slot replacement is needed). Concrete calls spell explicit argument mode markers (`E0405` if omitted, `E0406` if mismatched, `E0410` if `mut`/`^mut` targets a non-addressable expression):

| Formal parameter | Call-site marker | Authority & obligation |
| :--- | :---: | :--- |
| `x: T` | `expr` or `\|>` | Deeply immutable snapshot or value copy (`E0535` on live writer) |
| `ref x: T` | `ref expr` or `\|> ref` | Scoped read-only borrow of shared object (`E0401` on value type `T`) |
| `mut x: T` | `mut place` or `\|> mut` | Temporary exclusive write access; requires reachable write (`E0527`, `&mut`) |
| `^mut x: T` | `^mut place` or `\|> ^mut` | Shared writable handle; requires reachable retention beyond temporary call access (`E0527`; `&^mut` beyond root return) |
| `new x: T` | `new expr` or `\|> new` | Transfers construction/resource ownership (`E0548` on borrowed/shared input; ends `expr` with `E0549`; `E0411` on plain value types) |
| `via x: T` | Mode-dependent | Instantiates static mode template from caller's supplied mode |

```ril
fn bump_node(mut n: Node) &mut -> () { n.val += 1 }
fn consume_node(new n: Node) -> int { n.val }

fn test_params() -> () {
    let mut n0 = Node.{ val: 5 }
    bump_node(mut n0)
    -- bump_node(n0)                    -- Error [E0405]: missing 'mut' marker at call site
    -- bump_node(ref n0)                -- Error [E0406]: argument mode 'ref' does not match 'mut'
    -- bump_node(mut Node.{ val: 1 })   -- Error [E0410]: 'mut' requires an addressable writable place
    -- bump_node(mut n0, 1)             -- Error [E0314]: arity mismatch (expected 1, got 2)
    -- let _ = consume_node(new n0)     -- Error [E0548]: 'n0' lost construction qualification after borrow
}
test_params()
-- fn bad_var(var x: int) -> () { x = 1 }     -- Error [E0403]: 'var' parameter prohibited
-- fn bad_new_val(new x: int) -> int { x }    -- Error [E0411]: 'new' prohibited on value type 'int'
```

#### Default Parameters and Named Arguments

| Default & label rule | Requirement |
| :--- | :--- |
| Permitted default modes (`E0404`) | Plain, `ref`, and `meta` parameters on `FunctionDecl`, `MetaFnDecl`, and `AnonFnExpr` may declare `= default_expr`; defaults on `mut`, `^mut`, `new`, or `via` parameters fail `E0404: MutableParameterDefaultProhibitedError` |
| Scope & purity (`E0408`, `E0409`, `E0910`) | Defaults may reference earlier parameters in declaration order (`E0408: InvalidDefaultParameterReferenceError` on self or forward parameter references) and must be pure (`E0409: ImpureParameterDefaultError` on `@Eff` or mutable/live/foreign state). Exported callables require referenced module bindings to satisfy `E0910`; publishing a default closure capturing an earlier parameter charges `&capture` at the caller (`E0510`) |
| Named & positional binding (`E0325`, `E0339`, `E0314`) | Explicit arguments evaluate left-to-right in written order, followed by omitted defaults in parameter order. Positional arguments bind the next unbound parameter; `label: expr` binds parameter `label` (`E0339: UnknownNamedArgumentError` if unknown, `E0325: DuplicateArgumentError` if already bound, `E0314` if required parameters remain unbound, `E0338` if callee is non-callable) |
| `CallableType` boundary | `CallableType` carries optional parameter labels by position and strips default expressions (`E0314` when omitted through a `CallableType` handle) |

```ril
fn connect(host: str, port: int = 8080, tls: bool = true) -> str {
    "{host}:{port} (tls={tls})"
}
fn step_from(start: int, delta: int = start) -> int { start + delta }

fn test_defaults() -> () {
    assert(connect("db.local", tls: false) == "db.local:8080 (tls=false)")
    assert(step_from(5) == 10)
    -- connect("db.local", host: "dup")       -- Error [E0325]: parameter 'host' bound twice
    -- connect("db.local", prt: 90)           -- Error [E0339]: unknown parameter label 'prt'
}
test_defaults()
-- fn bad_mut_def(mut n: Node = Node.{ val: 0 }) &mut -> () { n.val += 1 } -- Error [E0404]
-- fn bad_fwd_def(a: int = b, b: int = 1) -> int { a + b }                 -- Error [E0408]
-- fn bad_io_def(s: str = { println("x"); "a" }) @Io -> str { s }          -- Error [E0409]
```

### Anonymous Functions, Trailing Closures, and Projection Accessors

```ebnf
AnonFnExpr    ::= "\" [ AnonParams ] [ EffectAnnot ] [ StateAnnot ] "->" Expression
AnonParams    ::= AnonParam { "," AnonParam } [ "," ]
AnonParam     ::= [ ParameterMode ] ( ValueName | Wildcard ) [ ":" TypeExpression ] [ "=" Expression ]
AccessorExpr  ::= "\" AccessorNav AccessorField { AccessorNav AccessorField }
AccessorNav   ::= "." | "?."
AccessorField ::= FieldLabel | TupleIndex
```

- **Trailing Closures**: A `CallExpr` may pass its final callable argument as a trailing `AnonFnExpr` or `AccessorExpr` directly after `(...)`—or omit empty `()` when the callable is the sole argument (`absorb_panic \-> { ... }`, `AsyncRt::scope \mut s -> { ... }`). Postfix `?` chains directly onto trailing-closure calls.
- **Shorthand Projection Accessors (`\.field`, `\.0`, `\?.field`)**: Desugar to unary pure closures (`\x -> x.field`, `\x -> x.0`, `\x -> x?.field`) over records, nominal wrappers, tuples, and single-variant narrowed sums (`E0336` on unknown field, `E0312` on out-of-bounds tuple index, `E0337` on collections or unnarrowed sums). Any `?.` segment lifts the result to `?T`.

```ril
type Dept = .{ name: str, code: (str, int) }
type Org  = .{ title: str, dept: ?Dept }

fn with_tx<T>(mut log: []str, body: fn(mut []str) @& -> Result<T, str>) &mut -> Result<T, str> {
    Array::push(mut log, "begin")
    let out = body(mut log)?
    Array::push(mut log, "commit")
    Ok out
}

fn test_closures_and_accessors() -> Result<int, str> {
    let orgs = [
        Org.{ title: "Core", dept: Some Dept.{ name: "Infra", code: ("INF", 10) } },
        Org.{ title: "Labs", dept: None },
    ]
    assert((orgs |> Array::map(\.title)) == ["Core", "Labs"])
    assert((orgs |> Array::map(\.dept?.code.1)) == [Some 10, None])

    let mut log: []str = []
    let code = with_tx(mut log) \mut entries -> {
        Array::push(mut entries, "insert")
        Ok 200
    }?
    assert(log == ["begin", "insert", "commit"])
    Ok code
}
assert(test_closures_and_accessors() == Ok 200)
```

### Closures and Lexical Environments

Closures capture enclosing bindings by minimum required authority; returning or storing a closure that captures non-pure enclosing runtime variables or stateful lexical handlers requires `&capture` on the enclosing named function (`E0510`), and its `CallableType` carries `&up` (or requires a `mut` / `^mut` handle when mutating captured state):

```ril
type CounterCell = .{ var value: int }
type Step = fn() &up -> int

fn make_counter(^mut cell: CounterCell) &capture &^mut &return{^mut cell} -> new Step {
    \-> {
        cell.value += 1
        cell.value
    }
}

fn test_counter() -> () {
    let mut c = CounterCell.{ value: 0 }
    let ^mut step = make_counter(^mut c)
    assert(step() == 1 && step() == 2 && c.value == 2)
}
test_counter()
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
- **`&mut`**: Required on named functions that may mutate a `mut`, `^mut`, or `new` parameter (`E0510`).
- **`&^mut`**: Required when a `^mut` parameter (or locally allocated shared root) is retained into another parameter, closure environment, or non-root structure (`E0510`; root `-> ^mut(x) T` already accounts for its own return retention).
- **`&capture`**: Required when a named function returns or stores a newly created closure environment capturing non-pure runtime locals/parameters (`E0510`; pure immutable captures require `&capture` on the factory definition while matching pure `fn(...) -> ...` targets).
- **Minimal Annotations (`E0529: ExcessiveStateAnnotationError`)**: Named `fn` declarations must not spell `&mut`, `&^mut`, `&capture`, `&up{...}`, or `&return{...}` clauses that are not actually exercised by the body (`E0529`, including redundant `&^mut` alongside bare root `-> ^mut(x) T`).

```ril
-- fn excess_mut(ref c: Node) &mut -> int { c.val }            -- Error [E0529]: '&mut' not exercised by body
-- fn dup_share(^mut c: Node) &^mut -> ^mut(c) Node { c }      -- Error [E0529]: root '^mut(c)' already covers return retention
```

### State Groups and Captured Layers

Block-local named `fn` declarations that access enclosing local bindings spell `&up{...}` listing the captured outer bindings (`&up{limit}`, `&up{ref view}`, `&up{mut buf}`; malformed groups fail `E0538`, unused items fail `E0529`). Module-level and `sub`-level functions never carry `&up{...}` because module/`sub` top-level forbids mutable or live state (`E0906`) and reading pure `let` / `meta let` constants requires **no** state annotation.

```ril
let GLOBAL_FACTOR = 3                  -- Pure module constant

fn scale_all(xs: []int, offset: int) -> []int {
    fn transform(x: int) &up{offset} -> int {
        x * GLOBAL_FACTOR + offset     -- GLOBAL_FACTOR needs no '&up'; outer local 'offset' uses '&up{offset}'
    }
    -- fn bad_up(x: int) &up{ghost} -> int { x }  -- Error [E0538]: unknown outer source 'ghost' in '&up{...}'
    -- fn idle_up(x: int) &up{offset} -> int { x } -- Error [E0529]: excessive '&up{offset}' not read by body
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
| Wrapping/coerce container element mode from `[]T` / `[ref]T` to `[mut]T` / `[^mut]T` | `E0522` |
| Passing two `mut` arguments (or `mut` + `^mut`) with potentially overlapping reachable origins | `E0523` |
| Passing `mut` alongside plain/`ref` observation of potentially overlapping reachable origins | `E0524` |
| Mutating a collection while iterating over it in `for` | `E0526` |
| Returning `mut` / `^mut` / `new` authority from immutable/`ref` or temporary `mut` sources | `E0528` |

```ril
type Box = .{ var n: int }
fn swap_add(mut a: Box, mut b: Box) &mut -> () { a.n += b.n; b.n += 1 }
fn observe_mut(mut a: Box, ref b: Box) &mut -> int { a.n += 1; b.n }

fn test_exclusivity() -> () {
    let mut x = Box.{ n: 1 }
    x.n += 1
    -- swap_add(mut x, mut x)              -- Error [E0523]: overlapping mut-mut origins
    -- let _ = observe_mut(mut x, ref x)   -- Error [E0524]: overlapping mut-ref hazard
    -- let mut bad_elems: [mut]Box = [Box.{ n: 1 }] |> \xs: []Box -> xs -- Error [E0522]: container element mode laundering
    let mut items = [1, 2, 3]
    Array::push(mut items, 4)
    -- for ref items as v { Array::push(mut items, v) } -- Error [E0526]: mutating 'items' during 'for' iteration
}
test_exclusivity()
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

`absorb_panic` contains synchronous defects behind an unwind-safe boundary, running active `with let` cleanup handlers inside the protected closure before returning `Err (PanicError::Panicked info)`.

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

fn test_absorb() -> () {
    assert(isolated_parse(["k", "v"]) == Ok "v")
    let Err (PanicError::Panicked info) = isolated_parse(["only_one"]) else { panic("expected panic") }
    assert(len(panic_message(info)) > 0)
    let mut ext = [1, 2]
    Array::push(mut ext, 3)
    -- let _ = absorb_panic \-> Array::push(mut ext, 4) -- Error [E0608]: unwind-unsafe external 'mut' access
}
test_absorb()
```

| `absorb_panic` rule | Requirement |
| :--- | :--- |
| Unwind safety (`E0608`) | `action` must not observe or mutate external `mut`/`^mut`/`ref` state, access `.d.ril` `opaque` handles, emit unhandled operational effects (including `@Io` / `@Async`), or leak mutable/`with let` captures (`E0608`). Confined local `var` / `let mut` / `with let` state and locally handled pure `eff` operations are allowed |
| Sealed `PanicInfo` (`E0301`, `E0308`) | `PanicInfo` is an opaque prelude type (`E0301` on direct construction, `E0308` on representation penetration); `panic_message(info)` extracts the diagnostic message at run time (`E0810` in static evaluation) |
| Double-Fault termination | If a `with let` cleanup handler panics while unwinding an earlier panic, the runtime terminates the OS process immediately without returning `Err` |

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
pub opaque type Sender<T |> Sendable> with close
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
| `Sendable` (`E0301`) | Admits value types, `.ril` shared objects without `ref`/`^mut` members whose constituents are `Sendable`, `Sender<U>` / `Receiver<U>`, and pure/stateless callables limited to `@Io`, `@Async`, and pure `fn` effects; rejects `Scope`, `Task`, `Draft`, `with let` bindings, and `.d.ril` `opaque` handles |
| Cross-fiber isolation (`E0601`, `E0615`, `E0549`) | Fiber closures forbid `ref`, `mut`, `^mut`, `var`, or `with let` captures (`E0601`) and stateful outer `fn` handlers (`E0615`); `@Io`, `@Async`, and pure stateless `fn` handlers cross fibers. Direct single-shot closures (`run`, `spawn`, `zip`, `try_zip`, `race`, `supervise`, `timeout_ms`) may move outer `new` bindings once (`E0549` on parent reuse) |
| Lexical region $\sigma$ (`E0604`) | Each `scope` / `try_scope` creates a fresh static region $\sigma$ shared by its `Scope` parameter and spawned `Task<T>` handles. Neither `Scope` nor `Task<T>` may escape `body` or cross into another nursery's `join`/`cancel` (`E0604`). Normal `scope` exit awaits unjoined tasks in reverse spawn order; `try_scope` `Err` cancels and drains siblings |
| `Result` inspection & supervision (`E0720`, `E0608`) | `Task<Result<T, E>>` must be `join`ed (inspecting its `Result`) or `cancel`ed (`E0720`); `Receiver<Result<T, E>>` requires `drain` (`close_recv` fails `E0720`); `try_*`, `race`, `timeout_ms`, and `supervise` reject nested `Result` payloads (`E0720`). `supervise` enforces unwind safety (`E0608`) |

---

## Compile-Time Computation and Introspection

### Static Type Values and Type Quotation

`Type<T>` is the exact static metatype representing type `T`; `<T>` quotes `T` as a static token value, and `<tok>` inside a type expression unquotes a static token back into a type. Bare `Type` in value annotations or bare type names in value expressions (`let x = int`) fail `E0319`. Type-function parameters support trailing defaults (`E0316` if non-trailing, `E0320` on self/forward references).

```ebnf
TokenType        ::= "Type" "<" TypeExpression ">"
TypeFunctionExpr ::= "\" TypeFnParam { "," TypeFnParam } "->" Expression
TypeFnParam      ::= PascalCase [ TypeConstraint ] [ "=" TypeExpression ]
                   | ValueName [ ":" TypeExpression ] { "|>" PipelineConstraint } [ "=" Expression ]
                   | ModeParamDecl
```

```ril
type Nullable = \T = int -> <?T>
type Unpack = \T -> {
    let tok: Type<T> = <T>
    <.{ item: <tok> }>
}
type OptInt = Nullable<>
meta let _ = assert(<OptInt> == <?int> && <int> != <f64>)
-- let bad_bare = int                  -- Error [E0319]: bare type in value expression; write '<int>'
```

### Pure Type Functions and Result Restrictions

<a id="finite-evaluation-with-div"></a>

```ebnf
MetaLetDecl ::= [ Visibility ] "meta" "let" ( ScreamingSnakeCase | Wildcard ) [ ":" TypeExpression ] "=" Expression
MetaFnDecl  ::= { MetaAttr } [ Visibility ] "meta" "fn" ValueName [ GenericParams ]
                "(" [ ParameterList ] ")" ReturnSpec [ SignatureWhereClause ] Block
```

- **Pure Static Domain (`E0335`, `E0812`, `E0813`, `E0816`)**: `TypeFunctionExpr`, `meta fn`, and `meta let` evaluate in a pure compile-time environment with local `var`/`let mut`, loops, and recursion, forbidding `@Eff` / `&State` annotations (`E0335` on type functions, `E0813` on `meta fn`). `meta fn` cannot return `Type<T>` tokens (`E0812`). Run-time values, parameters, storage, and closures cannot materialize `Type<T>` (`E0816`).
- **Compiler Root Evaluation Budget (`E0811`, `E0830`, `E0831`)**: Every compile-time root evaluation (`type` application, pipeline guard, `meta let`, `meta(...)`, const generic argument, and compile-time folded `meta fn` call) executes under a configured deterministic step budget, charging 1 unit per function/closure entry and loop iteration. Exhausting the budget rejects compilation with uncatchable `E0811` (partial type previews in diagnostics are informational only). Failed static `assert` fails `E0830`; static `panic` or arithmetic defects fail `E0831`.

```ril
meta fn align_up(n: int, align: int = 4096) -> int {
    assert(n >= 0 && align > 0)
    ((n + align - 1) / align) * align
}
meta let PAGE = align_up(3000)
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
TypeProjection            ::= PrimaryType "." ( FieldLabel | PascalCase | TupleIndex | "(" Expression ")" )
MappedRecordType          ::= ".{" [ ModeModifier ] MappedComprehensionClause ":" TypeExpression "}"
MappedComprehensionClause ::= "[" ForIterable "as" Pattern "]"
ModeModifier              ::= MemberMode | ValueName
```

- **Constituent Projection (`T.(k)`)**: Projects field type `T.field` / `T.("field")` on transparent records, component type `T.0` / `T.(0)` on tuples, and payload type `T.Variant` / `T.("Variant")` on transparent sums (`()` for unit variants; `E0308` on sealed `opaque` types).
- **Product Coordinates & Sum Variants (`coords`, `variants`)**:
  - `coords(<T>) -> [](MemberMode, CoordKey<T>)` enumerates `(mode, field_name)` pairs in UTF-8 byte order for transparent records (`CoordKey<T>` = `str`) and `(let, index)` pairs in ascending index order for tuples (`CoordKey<T>` = `int`; `()` yields `[]`) (`E0358` on non-products; `E0308` when sealed).
  - `variants(<T>) -> []str` enumerates deduplicated variant names in UTF-8 byte order for closed transparent sums (`E0301` on non-sums; `E0308` when sealed or open `..`).
- **Mapped Record Types (`.{ [m] [expr as pat]: Type }`)**: Comprehension keys must have type `str` (`E0341`), duplicate generated field names fail `E0210`, value-type fields with `mut`/`^mut`/`ref` modes fail `E0402`, and invalid mode sorts fail `E0356` / `E0357`.
- **Metadata Introspection (`ril/reflect`)**:
  - `Reflect::attrs<T, A>(target: Type<T>) -> []A`
  - `Reflect::field_attrs<T, A>(target: Type<T>, meta key: str |> Key<UnwrapOrSelf<T>>) -> []A`
  - `Reflect::variant_attrs<T, A>(target: Type<T>, meta variant: str) -> []A`
  - `Reflect::has_default<T>(target: Type<T>, meta key: str |> Key<UnwrapOrSelf<T>>) -> bool` (`true` iff `T` is a transparent nominal or opaque record whose root field `key` declares `= expr`; `false` on structural aliases)

```ril
type Select = \T: .{ ..R }, keys: []str -> {
    let chosen = coords(<T>) |> Array::filter(\(_, k) -> Array::contains(keys, k))
    <.{ m [chosen as (m, k)]: T.(k) }>
}

type Model = .{ id: int, var title: str, mut rows: []int }
type Patch = Select<Model, ["title", "rows"]> -- .{ var title: str, mut rows: []int }
type Args  .{ query: str, limit: int = 10 }
meta let _ = assert(Reflect::has_default(<Args>, "limit") && !Reflect::has_default(<Args>, "query"))
meta let _ = assert(len(coords(<(int, str)>)) == 2)
-- meta let _ = coords(<int>)            -- Error [E0358]: 'coords' requires a transparent record or tuple type
-- type BadMap = .{ [[1, 2] as k]: int } -- Error [E0341]: mapped record key must have type 'str'
-- type BadIdx = (int, str).(-1)         -- Error [E0815]: negative static tuple coordinate '-1'

fn read_field<T: .{ .. }>(via rec: T, meta key: str |> Key<T>) -> infer T.(key) {
    rec.(key)
}
fn test_introspection() -> () {
    let m = Model.{ id: 9, title: "init", rows: [1] }
    assert(read_field(m, "title") == "init")
}
test_introspection()
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
RigidNominalPattern   ::= { "Super" "::" } { RigidPatternSegment "::" } RigidPatternSegment
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

Ril enforces a **one-file-one-module** model with pure constant top-level initialization and non-generic hermetic inline `sub` namespaces:

```ebnf
SourceFile ::= ModuleFile | DeclFile
ModuleFile ::= { ModuleItem Separator } [ ModuleItem ] EOF
DeclFile   ::= { DeclUnitItem Separator } [ DeclUnitItem ] EOF
ModuleItem ::= UseDecl | SubDecl | FunctionDecl | MetaFnDecl | MetaLetDecl
             | LetDecl | OpaqueTypeDecl | TypeDecl | NominalDecl
             | SumTypeDecl | EffectDecl
SubDecl    ::= { MetaAttr } [ Visibility ] "sub" PascalCase "{" { SubItem Separator } [ SubItem ] "}"
SubItem    ::= ModuleItem
Visibility ::= "pub" [ "(" "pkg" ")" ]
```

| Compilation unit / scope | Role & rules |
| :--- | :--- |
| **Executable Root (`.ril`)** | Entry file of an executable build: non-`sub`, unimportable (`E0208`), forbids root `pub` / `pub(pkg)` (`E0905`), and requires a private root `fn main` (`E0903`, `E0904`) |
| **Library Module (`.ril`)** | Importable `sub` named `to_pascal_case(file_stem)`; forbids `fn main` (`E0904`). Items default to file-private (`E0201`); files with zero root `pub` items have `pub(pkg)` module visibility (`E0201` externally) |
| **External Interface (`.d.ril`)** | Bodyless foreign host declarations (`E0901` on bodies or `=` on `opaque type`); forbids `fn main` (`E0904`); `DeclSub` enforces `.d.ril` rules recursively |
| **Inline `sub` (`[Visibility] sub Name`)** | Non-generic `PascalCase` namespace at file or `sub` top-level (`E0703` in statements, `E0702`/`E0704` in `where`, `E0203` on `sub Super`, `E0904` on `fn main`). Hermetic scope: only Prelude is ambient; `Super::` accesses enclosing file/`sub` items (`E0208` at file root); downward access requires `pub` or same-package `pub(pkg)` (`E0201`); `opaque type` transparency stays strictly within its exact defining file or `sub` (`E0308`) |
| **Top-Level Purity (`E0202`, `E0906`, `E0205`)** | File and `sub` top-level allow only pure deeply immutable `ScreamingSnakeCase` constants (`let` and `meta let`, requiring zero `&up` annotations when read). Mutable, shared, live `ref`, or `with let` top-level bindings (`var`, `let mut`, `let ^mut`, `let ref`, `with let`) are prohibited (`E0906`); impure initializers fail `E0202`; top-level `?` fails `E0205` |

```ril
-- File: math/circle.ril
pub let PI = 3.141592653589793
pub(pkg) let INTERNAL_EPS = 1.0e-9
type Hidden = .{ r: f64 }

pub fn area(r: f64) -> f64 { PI * r * r }       -- Zero '&up' needed for pure module constant 'PI'
pub(pkg) fn label_pkg(pkg: str) -> str { pkg }  -- 'pkg' is contextual in pub(pkg) and free as an identifier

pub sub UnitCircle {
    pub opaque type Rad = f64
    pub fn circumference() -> f64 { 2.0 * Super::PI } -- Hermetic 'sub' reaches parent 'PI' via 'Super::'
    -- let _ = PI                               -- Error [E0204]: 'PI' not in scope without 'Super::'
}
-- let _r: UnitCircle::Rad = 1.0                -- Error [E0308]: 'Rad' is sealed outside 'UnitCircle'
-- use Super::PI                                -- Error [E0208]: file root has no enclosing 'Super'
-- pub fn leak() -> Hidden { Hidden.{ r: 1.0 } } -- Error [E0910]: 'pub' signature leaks private 'Hidden'
-- var global_hits = 0                          -- Error [E0906]: top-level mutable state is prohibited
-- let BOOT_TS = Clock::now()                   -- Error [E0202]: top-level initializer must be pure
```

### Module Imports and Visibility

```ebnf
UseDecl     ::= [ Visibility ] "use" FilePath [ "as" PascalCase ]
              | [ Visibility ] "use" ModulePath "::" ( "{" ImportList "}" | "*" | ImportItem )
PackageRoot ::= "pkg" | "ril" | SnakeCase
FilePath    ::= PackageRoot "/" SnakeCase { "/" SnakeCase }
ModulePath  ::= FilePath { "::" PascalCase }
              | "Super" { "::" "Super" } { "::" PascalCase }
              | PascalCase { "::" PascalCase }
ImportList  ::= ImportItem { "," ImportItem } [ "," ]
ImportItem  ::= Identifier [ "as" Identifier ]
```

- **Package Roots & `to_pascal_case` (`E0208`, `E0209`, `E0102`)**: `pkg/...` resolves inside the current package, `ril/...` resolves standard-library modules, and `<dep>/...` resolves mounted dependencies (mount names `pkg` and `ril` are prohibited; missing modules or bare single-segment paths fail `E0208`; absent members fail `E0209`). Unaliased `use pkg/http_server` binds `HttpServer` (`to_pascal_case("http_server")`), enforcing acronym title-casing (`a_b` and `sha_256` fail `E0102`, `super.ril` fails `E0203`).
- **Visibility Lattice & Interface Consistency (`E0201`, `E0910`)**: `private < pub(pkg) < pub`; effective visibility along an inline `sub` path is capped by every enclosing `sub`. Re-exports (`pub use`) cannot widen target visibility (`E0201`). Any `pub` or `pub(pkg)` declaration's expanded signature, non-opaque fields/variants, `TypeFunctionExpr` body, parameter/field defaults, `with` cleanup function, and unhandled `@Eff` must have visibility $\ge$ the declaration's effective visibility (`E0910`; `pub opaque` internal representations remain private).

```ril
use pkg/math/circle as Circle
use pkg/math/circle::UnitCircle
-- use pkg/math/missing                -- Error [E0208]: module 'pkg/math/missing' not found
-- use pkg/math/circle::nonexistent    -- Error [E0209]: 'nonexistent' not found in 'Circle'
-- let _ = Circle::Hidden.{ r: 1.0 }   -- Error [E0201]: 'Hidden' is private to 'Circle'
-- use pkg/net/a_b                     -- Error [E0102]: derived 'AB' violates PascalCase acronym rule
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
-- sub Sub { fn main() -> () {} }             -- Error [E0904]: 'main' prohibited inside 'sub'
-- pub let ROOT_EXPORT = 1                    -- Error [E0905]: 'pub' prohibited in executable root
```

`main` must be a non-public, non-generic ordinary `fn` at the executable root taking `()` and returning `()` or `Result<(), str>` (`E0903` if missing, `E0904` if malformed or inside `sub`). It may declare `@Io` and `@Async` (`E0612` on unhandled user-defined `eff`). Returning `()` / `Ok ()` exits `0`; returning `Err msg` prints `msg` + `\n` to stderr and exits `1`.

### Prelude Scope

The ambient prelude encloses every compilation unit and inline `sub`, predeclaring primitive types, `Option<T>` (`Some T`, `None`), `Result<T, E>` (`Ok T`, `Err E`), `Set<T>`, `PanicInfo`, `PanicError`, `MemberMode`, `Draft<T>`, `@Io`, `@Async`, static guards/operations `SharedObject`, `Sendable`, `LenTarget`, `Tuple`, `NominalWrapper`, `Unwrap`, `UnwrapOrSelf`, `CoordKey`, `Key`, and core modules `Array`, `Map`, `Set`, `String`, `Bytes`, `Numeric`, `Reflect`. Explicit imports (`use ril/io`, `use ril/file`, `use ril/os`, `use ril/async`, `use ril/async/channel`, `use ril/platform`, `use ril/math`, `use ril/crypto`) bring system, concurrency, and platform APIs into scope.

#### Built-in Foundational Operations

| Built-in | Canonical signature | Phase & contract |
| :--- | :--- | :--- |
| `len` | `pub fn len<T \|> LenTarget>(via item: T) -> int` | Dual-phase: scalar count of `str`, byte count of `bytes`, element/entry count of `[]T`, `[K: V]`, `Set<T>` (admits `ref` on collections at run time; `E0401` on `ref str`) |
| `inner` | `pub fn inner<W \|> NominalWrapper>(via wrapper: W) -> infer Unwrap<W>` | Run-time: unwraps transparent `NominalDecl` wrapper to its payload (`()` for unit nominals; preserves `ref` observation; `E0308` when sealed, `E0301` on non-nominals) |
| `clone` | `pub fn clone<T \|> SharedObject>(via value: T) -> new T` | Run-time: deep copy of `SharedObject` (via snapshot or `ref`) into isolated `new T` (`E0301` on value or `.d.ril` `opaque` types, `E0530` on live closures) |
| `derive` | `pub fn derive<T \|> SharedObject>(base: T, recipe: fn(mut Draft<T>) @& -> ()) -> T` | Run-time: path-targeted functional update on immutable `SharedObject` (`E0536`, `E0607`) |
| `absorb_panic` | `pub fn absorb_panic<T>(via action: fn() @& -> infer T) -> infer Result<T, PanicError>` | Run-time: unwind-safe panic containment (`E0608`) |
| `panic_message` | `pub fn panic_message(info: PanicInfo) -> str` | Run-time: extracts human-readable message from `PanicInfo` (`E0810` in static eval) |
| `type_name` | `pub meta fn type_name<T>(token: Type<T>) -> str` | Static only: diagnostic display string of `T` |
| `coords` | `pub meta fn coords<T>(token: Type<T>) -> [](MemberMode, CoordKey<T>)` | Static only: `(mode, key)` pairs of transparent record (`str` keys) or tuple (`int` keys) `T` (`E0358` non-product, `E0308` sealed) |
| `variants` | `pub meta fn variants<T>(token: Type<T>) -> []str` | Static only: variant tags of closed transparent sum `T` (`E0301` non-sum, `E0308` sealed/open) |
| `panic` | `pub fn panic(message: str) -> never` | Dual-phase: LIFO panic unwinding at run time; `E0831` in static eval |
| `assert` | `pub fn assert(condition: bool, message: str = "assertion failed") -> ()` | Dual-phase: panics with `message` when `false` at run time; `E0830` when `false` in static eval |
| `print` / `println` | `pub fn print(text: str) @Io -> ()`<br>`pub fn println(text: str) @Io -> ()` | Run-time (`@Io`): writes UTF-8 text (plus `\n` for `println`) to stdout |

### Mandatory Inspection of Fallible Results

Every produced `Result<T, E>` carries a mandatory static inspection obligation (`E0720`): before normal scope exit, it must be matched (`match`, `if let`, `let ... else`), tag-tested via a reached `is` variant/subset pattern (`res is Ok _`), propagated (`?`), handled (`??`), or returned. Discarding a `Result` as an expression statement, binding it to `_`, testing `res is _`, or overwriting its last variable without tag inspection fails `E0720`.

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
    let r = write_entry("tested")
    assert(r is Ok ())                    -- OK: reached 'is' constructor test inspects Result
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
| **`E0305`** | [`NominalTypeMismatchError`](#nominal-type-alias-and-opaque-types) |
| **`E0306`** | [`KindMismatchError`](#generic-parameters-defaults-and-value-sorts) |
| **`E0307`** | [`MissingFieldError`](#record-types-and-row-polymorphism) |
| **`E0308`** | [`OpaqueBoundaryViolationError`](#nominal-type-alias-and-opaque-types) |
| **`E0309`** | [`VacuousBindingError`](#guarded-bindings) |
| **`E0310`** | [`InvalidatedNarrowingAccessError`](#flow-sensitive-type-narrowing) |
| **`E0311`** | [`ContradictoryNarrowingError`](#flow-sensitive-type-narrowing) |
| **`E0312`** | [`TupleIndexOutOfBoundsError`](#array-map-set-and-tuple-types) |
| **`E0313`** | [`CyclicTypeAliasError`](#definitional-equality-and-recursive-types) |
| **`E0314`** | [`ArityMismatchError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0315`** | [`EscapingLocalNominalTypeError`](#block-expressions-and-local-declarations) |
| **`E0316`** | [`NonTrailingDefaultGenericParamError`](#generic-parameters-defaults-and-value-sorts) |
| **`E0317`** | [`FunctionDefaultGenericProhibitedError`](#generic-parameters-defaults-and-value-sorts) |
| **`E0318`** | [`LiteralTypeProhibitedError`](#generic-parameters-defaults-and-value-sorts) |
| **`E0319`** | [`BareTypeInExpressionContextError`](#static-type-values-and-type-quotation) |
| **`E0320`** | [`ForwardTypeDefaultReferenceError`](#generic-parameters-defaults-and-value-sorts) |
| **`E0321`** | [`NormallyCompletingElseError`](#guarded-bindings) |
| **`E0322`** | [`WildcardExpressionError`](#identifiers-and-casing-invariants) |
| **`E0323`** | [`ConstGenericSortMismatchError`](#generic-parameters-defaults-and-value-sorts) |
| **`E0324`** | [`DynamicRecordIndexProhibitedError`](#record-types-and-row-polymorphism) |
| **`E0325`** | [`DuplicateArgumentError`](#default-parameters-and-named-arguments) |
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
| **`E0337`** | [`NonProductProjectionError`](#indexing-slicing-and-static-coordinate-projection); [Anonymous Functions, Trailing Closures, and Projection Accessors](#anonymous-functions-trailing-closures-and-projection-accessors) |
| **`E0338`** | [`NonCallableInvocationError`](#default-parameters-and-named-arguments) |
| **`E0339`** | [`UnknownNamedArgumentError`](#default-parameters-and-named-arguments) |
| **`E0340`** | [`GenericArityMismatchError`](#generic-parameters-defaults-and-value-sorts) |
| **`E0341`** | [`InvalidRecordKeySortError`](#static-introspection) |
| **`E0344`** | [`InsufficientTypeInformationError`](#generic-parameters-defaults-and-value-sorts); [Anonymous Generalization and Fixed Storage](#anonymous-generalization-and-fixed-storage) |
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
| **`E0359`** | [`InvalidFieldDefaultPlacementError`](#record-types-and-row-polymorphism) |
| **`E0360`** | [`UnfinishedExpressionHoleError`](#expression-grammar-and-precedence) |
| **`E0361`** | [`DivisionOrShiftDomainError`](#arithmetic-bitwise-relational-and-logical-operators) |

### Parameters, Argument Modes, and Defaults

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0401`** | [`ValueTypeReferenceParameterError`](#value-types) |
| **`E0402`** | [`ValueTypeReferenceModeError`](#value-types) |
| **`E0403`** | [`VarParameterProhibitedError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0404`** | [`MutableParameterDefaultProhibitedError`](#default-parameters-and-named-arguments); [Record Types and Row Polymorphism](#record-types-and-row-polymorphism) |
| **`E0405`** | [`MissingArgumentModeMarkerError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0406`** | [`InvalidArgumentModeError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0407`** | [`CallableParameterModeMismatchError`](#callable-contract-matching) |
| **`E0408`** | [`InvalidDefaultParameterReferenceError`](#default-parameters-and-named-arguments); [Record Types and Row Polymorphism](#record-types-and-row-polymorphism) |
| **`E0409`** | [`ImpureParameterDefaultError`](#default-parameters-and-named-arguments); [Signature Value Contracts](#signature-value-contracts); [Record Types and Row Polymorphism](#record-types-and-row-polymorphism) |
| **`E0410`** | [`InvalidMutableArgumentTargetError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0411`** | [`InvalidConstructionParameterError`](#parameter-modes-caller-obligations-and-defaults) |
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
| **`E0527`** | [`UnusedAuthorityError`](#reachable-authority-use) |
| **`E0528`** | [`ReturnMutabilityLaunderingError`](#exclusivity-and-anti-laundering-matrix) |
| **`E0529`** | [`ExcessiveStateAnnotationError`](#local-state-discharge-parameter-mutation-and-sharing) |
| **`E0530`** | [`IllegalNonClonableAuthorityError`](#deep-immutability) |
| **`E0531`** | [`InvalidRefOriginError`](#subtyping-reception-and-contract-compatibility) |
| **`E0532`** | [`ReassignableScopedResourceError`](#scoped-resource-bindings) |
| **`E0533`** | [`AliasedNarrowingHazardError`](#flow-sensitive-type-narrowing) |
| **`E0534`** | [`CallableContractMismatchError`](#callable-contract-matching) |
| **`E0535`** | [`NonImmutableBindingError`](#deep-immutability) |
| **`E0536`** | [`InvalidDeriveInputError`](#functional-updates-via-derive) |
| **`E0537`** | [`LiveArrayInvalidationError`](#indexing-slicing-and-static-coordinate-projection) |
| **`E0538`** | [`InvalidStateSourceGroupError`](#state-groups-and-captured-layers) |
| **`E0541`** | [`InvalidScopedCleanupContractError`](#scoped-resource-bindings) |
| **`E0543`** | [`UnanchoredRefOriginError`](#subtyping-reception-and-contract-compatibility) |
| **`E0544`** | [`MissingInferredFunctionAnnotationError`](#mandatory-contract-inference-and-completion); [Signature Value Contracts](#signature-value-contracts) |
| **`E0545`** | [`InvalidReturnSourceContractError`](#return-construction-access-modes-and-sources) |
| **`E0546`** | [`InvalidNewReturnContractError`](#return-construction-access-modes-and-sources) |
| **`E0547`** | [`InvalidOpenRowPlacementError`](#closed-and-open-callable-rows) |
| **`E0548`** | [`InvalidConstructionInputError`](#parameter-modes-caller-obligations-and-defaults) |
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
| **`E0616`** | [`ScopedCleanupEffectError`](#scoped-resource-bindings) |
| **`E0618`** | [`UndischargedLocalEffectError`](#block-expressions-and-local-declarations) |
| **`E0620`** | [`InvalidEffectLabelError`](#built-in-system-effects) |
| **`E0621`** | [`InvalidHandlerTargetError`](#effect-declarations-and-handlers) |
| **`E0622`** | [`DuplicateHandlerOperationError`](#effect-declarations-and-handlers) |

### Declaration Contexts, Control Flow, and Fallible Values

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0701`** | [`ChainedAssignmentProhibitedError`](#record-construction-and-assignments) |
| **`E0702`** | [`InvalidWhereItemError`](#block-expressions-and-local-declarations) |
| **`E0703`** | [`IllegalSequentialDeclarationError`](#block-expressions-and-local-declarations) |
| **`E0704`** | [`InvalidSignatureWhereItemError`](#dual-tier-where-invariants) |
| **`E0705`** | [`DownwardScopeReferenceError`](#dual-tier-where-invariants) |
| **`E0706`** | [`SignatureTypeNotInSignatureWhereError`](#dual-tier-where-invariants) |
| **`E0707`** | [`InvalidControlTransferContextError`](#conditional-and-loop-expressions) |
| **`E0708`** | [`InvalidMetadataPlacementError`](#declaration-metadata-attributes) |
| **`E0710`** | [`IllegalControlTransferInFallbackError`](#pipeline-and-fallible-operators) |
| **`E0711`** | [`InvalidResultFallbackError`](#pipeline-and-fallible-operators) |
| **`E0712`** | [`InvalidPropagationOperandError`](#pipeline-and-fallible-operators); [Signature Value Contracts](#signature-value-contracts) |
| **`E0713`** | [`IncompatiblePropagationTargetError`](#pipeline-and-fallible-operators); [Signature Value Contracts](#signature-value-contracts) |
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
| **`E0814`** | [`StaticValueRequiredError`](#generic-parameters-defaults-and-value-sorts) |
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
