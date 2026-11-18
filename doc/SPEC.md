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
| Binding / access | `let`, `var`, and `use` govern slot lifetime and replacement; default, `ref`, `mut`, `^mut`, and `new` govern path access and authority |
| New regions / contained sources | `new` permits reception of newly constructed regions; nested old sources retain their permissions, aliasing, and declared return relations |
| Values / shared objects | `bool`, `int`, `f64`, `str`, `bytes`, and `()` copy by value; records, nonempty tuples, collections, and sums have GC-managed identity |
| Record forms / constructors | Named and anonymous records attach `.{...}` (`User.{ id: 1 }`); variant and non-record nominal constructors separate their payload with whitespace (`Ok 42`, `Ok ()`, `Some .{ x: 1 }`) |
| Aliases / nominal / opaque | `type A = B` is a structural alias; `nominal type A = B` has distinct public identity; `opaque type A = B` seals representation outside its defining file or `sub` |
| Reachable authority use | `var` requires reachable slot replacement, `mut` requires writable/consuming use, `^mut` parameters require surviving retention, and named state annotations must be minimal (`E0527`, `E0529`) |
| `where` / guards | Dual-tier `where` hoists helper declarations (`type`, `fn`, `meta fn`, block `eff`); `\|>` contracts validate static types and fallible runtime values |
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
    - [Structured Fiber Concurrency and Channels](#structured-fiber-concurrency-and-channels)
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
OneOrMore   ::= A+
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
| Authority independence | Object liveness grants no write authority; `use` deterministic cleanup is independent of GC |

### Failure Model and Purity

<a id="termination-and-halt-contracts"></a>

Ril separates expected domain failures from programming defects:

1. **Recoverable Errors (`!<T, E>` / `Result<T, E>` and `?T` / `Option<T>`)**: Carried as explicit values. Every `Result` must be inspected, propagated via `?`, or handled via `??` (`E0720`).
2. **Defects (`panic` / `assert`)**: Trigger deterministic LIFO stack unwinding, running active `use` cleanup handlers without requiring signature annotations. Unwind-safe boundaries (`absorb_panic`, `Fiber::supervise`) convert panics into `!<T, PanicError>` / `!<T, TaskFault>`.
3. **Purity**: A callable is pure when its normalized outward operational-effect row is empty and its outward state obligations reduce to empty after local discharge. Relations to deeply immutable return sources add no state effect but remain part of return-contract matching. `never` denotes computations with no normal continuation.

```ril
fn parse_port(s: str) -> !<int, str> {
    if s == "" { Err "empty port" } else { Ok 8080 }
}

fn connect_port(raw: str) -> !<int, str> {
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
| Secondary panic inside `use` cleanup during active panic/cancel unwinding | Immediate Double-Fault OS process termination (bypasses `absorb_panic`) |
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

- **Line continues** after binary/pipeline/fallback operators (`+`, `-`, `*`, `/`, `%`, `&`, `|`, `^`, `<<`, `>>`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `&&`, `||`, `|>`, `as`, `??`, `=`, `+=`, `-=`, `*=`, `/=`, `%=`, `&=`, `|=`, `^=`, `<<=`, `>>=`, `->`, `:`, `,`, `.`, `?.`, `::`) or inside unclosed `( ... )`, `[ ... ]`, `.{ ... }`, and committed `< ... >` / `!< ... >`.
- **Line continues** before `.field`, `?.field`, `|>`, `as`, `??`, `else`, `@`, `&`, `->`, or signature `where` on the next line (`use` and `with` never continue a preceding line; type-level `use <fn_name>` cleanup clauses must appear on the same line as the end of the type declaration). Inside `{ ... }`, `where` opens the trailing `BlockWhereClause`.
- **Tight lexical attachment & committed `< ... >`**: Call `(` (`f(x)`), index `[` (`xs[i]`, `xs?[i]`), named record `.{` (`User.{ id: 1 }`), result type `!<` (`!<T, E>`), and `@` / `&` annotations (`@io`, `@Clock`, `&mut`, `&up`; `@&` only when `&` is not followed by a state keyword) attach with no intervening whitespace/newline. `<` is committed in type/pattern/effect positions, at the start of an expression operand (`<TypeExpression>`), and when tightly attached after an identifier (`f<T>(x)`, `State<int>::get()`) with a matching `>` at the current delimiter depth; spaced `a < b` lexes as relational `<`. Closing a committed `< ... >` or `!< ... >` consumes one `>` character (`<!<int, str>>==<!<int, str>>`).

### Syntactic Diagnostic Conditions

| Code | Triggering condition |
| :---: | :--- |
| `E0120` | Unexpected token in the current syntactic production |
| `E0121` | Unexpected `EOF` while a construct remains incomplete |
| `E0122` | Unclosed `(`, `[`, `{`, `.{`, or committed `<` / `!<` delimiter |
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
PascalCase         ::= [A-Z]
                     | [A-Z] [a-z0-9]* [a-z] [a-z0-9]* { [A-Z] [a-z0-9]+ }
SnakeCase          ::= [a-z] { [a-z0-9] } { "_" [a-z0-9]+ }
ScreamingSnakeCase ::= [A-Z] [A-Z0-9]+ { "_" [A-Z0-9]+ }
                     | [A-Z] { [A-Z0-9] } "_" [A-Z0-9]+ { "_" [A-Z0-9]+ }
UnderscoreName     ::= "_" [a-z] { [a-z0-9] } { "_" [a-z0-9]+ }
Wildcard           ::= "_"
PathSegment        ::= PascalCase [ GenericArgs ]
QualifiedName      ::= { "Super" "::" } { PathSegment "::" } Identifier
```

- **Acronym Title-Casing & Casing Partition (`E0101`, `E0102`)**:
  - `PascalCase` is either a single uppercase letter (`T`, `U`, `K`, `V`, `M`) or a `_`-free identifier whose leading word starts with `[A-Z]` and contains `[a-z]` (`User`, `UserId`, `HttpServer`, `Sha256`, `Base64V2`; adjacent uppercase runs with lowercase such as `HTTPServer` or `UserID` fail `E0102`).
  - `ScreamingSnakeCase` contains no `[a-z]` and requires `_` or $\ge 2$ `[A-Z0-9]` characters (`PI`, `OS`, `UTF8`, `N_MAX`, `A_1`).
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

The following 29 reserved syntax keywords cannot be used as identifiers or field labels (`E0113`):

```text
as       break    continue eff      else     false    fn       for
if       infer    let      match    meta     mut      new      opaque
pub      ref      return   sub      true     type     typeof   use
var      via      where    while    with
```

- **Protected Names (`bool`, `int`, `f64`, `str`, `bytes`, `never`, `Type`, `Super`)**: Primitive type names cannot be used as identifiers or field labels (`E0113`), `Type` and `Super` cannot be redeclared or shadowed (`E0203`), and bare type names in runtime value expressions fail `E0319` (write `<int>`, `<never>`).
- **Contextual Identifiers (`pkg`, `ril`, `nominal`, `io`, `fiber`, `capture`, `up`)**: Ordinary `SnakeCase` identifiers in expressions, bindings, parameters, file paths, and record fields (`let fiber = 1`, `use ril/io`), recognized contextually inside `pub(pkg)`, `use pkg/...`, `use ril/...`, `nominal type`, `@io`, `@fiber`, `&capture`, and `&up` / `&up{...}`.

```ril
let pkg = "core"                       -- OK: contextual outside pub(pkg) and use pkg/...
let fiber = 1                          -- OK: contextual outside @fiber
-- let where = 1                       -- Error [E0113]: reserved keyword
-- let opaque = 1                      -- Error [E0113]: reserved keyword
-- let via = 1                         -- Error [E0113]: reserved keyword
-- type BadField = .{ fn: bool }       -- Error [E0113]: reserved keyword as field label
-- let int = 0                         -- Error [E0113]: intrinsic primitive type name
```

### Numeric Literals

Ril provides two numeric types: arbitrary-precision signed `int` and IEEE-754 binary64 `f64`. Numeric literals carry no width suffixes (`E0111` on malformed digits, trailing `_`, or invalid suffixes; `E0326` on `f64` literal magnitude overflow beyond finite binary64). Immediately after `.` or `?.`, decimal digits lex as individual `TupleIndex` tokens rather than `FloatLiteral` (`nested.0.1`).

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
                 | ResultType
                 | TokenType
                 | "(" TypeExpression ")"
                 | "<" Expression ">"
ResultType     ::= "!<" TypeExpression "," TypeExpression [ "," ] ">"
TypeReference  ::= QualifiedName [ GenericArgs ]
```

### Value Types

`bool`, `int`, `f64`, `str`, `bytes`, `()`, and `never` have no object identity and copy logically by value (implementations may share immutable backing buffers transparently). Value types forbid `ref`, `mut`, and `^mut` access modes in bindings, record fields, collection elements, and `ref`/`^mut` expressions (`E0402`), and in parameters/call markers (`E0401`).

```ril
let a = "hello"
let b = a                              -- Value copy
-- let ref bad_ref = a                 -- Error [E0402]: value type 'str' forbids 'ref'
-- fn bad_param(mut n: int) -> () {}   -- Error [E0401]: value type 'int' forbids 'mut' parameter
```

### Shared Object Types

Records (`.{...}`), nonempty tuples `(A, B)`, arrays `[M]T`, maps `[K: M V]`, `Set<T>`, and sum instances have heap allocation identity managed by tracing GC. Shared-object status permits aliasing of immutable snapshots (`let`) and explicit shared write handles (`^mut`), never implicit shared mutation.

### Record Types and Row Polymorphism

Record types, values, patterns, and mapped types uniformly use `.{...}`. Record fields may declare slot/access `MemberMode` modifiers (`var`, `mut`, `^mut`, `ref`, `var mut`, `var ^mut`, `var ref`), inferred `via` modes, or `[M]` for a static `MemberMode` value `M`. Root fields of `.ril` `nominal type` and `opaque type` record declarations may attach `meta(...)` attributes and pure default expressions (`= expr`).

```ebnf
RecordType      ::= ".{" [ RecordFieldList ] "}"
RecordFieldList ::= RecordTail
                  | RecordField { "," RecordField } [ "," RecordTail ] [ "," ]
RecordField     ::= { MetaAttr } [ RecordFieldMode ] FieldLabel ":" TypeExpression [ "=" Expression ]
RecordFieldMode ::= MemberMode | "via" | "[" StorageModeExpression "]"
FieldLabel      ::= ValueName
RecordTail      ::= ".." [ PascalCase ]
MemberMode      ::= "var" [ "mut" | "^mut" | "ref" ]
                  | "mut" | "^mut" | "ref"
```

- **Closed Records**: Exact field set (written order irrelevant). Duplicate labels fail `E0210`; missing fields without defaults fail `E0307`; unexpected fields fail `E0302`; reading an unknown field fails `E0336`; dynamic bracket indexing `rec[k]` fails `E0324`.
- **Row Polymorphism (`..R` / `..`)**: Opens a structural record type in generic bounds, transparent aliases, or direct callable parameters (`type WithId<R> = .{ id: int, ..R }`, `fn f(r: .{ id: int, .. }) -> int`). Non-record or nominal row instantiations fail `E0306` (unwrap nominal records via `inner` / `Unwrap<T>`); overlapping explicit labels and row remainder labels fail `E0212`; incompatible field modes fail `E0357`.
- **Root Record Field Defaults (`E0359`, `E0404`, `E0408`, `E0409`)**: `= expr` is permitted only on root fields of `.ril` `NominalTypeDecl` and `OpaqueTypeDecl` record declarations (`E0359` on transparent `type` aliases, nested, parameter, anonymous, or sum-payload records, and `E0901` in `.d.ril`). Defaults forbid `mut`/`^mut`/`ref`/`via` field modes (`E0404`; plain and `var` value/immutable fields are allowed), forbid self or forward field references (`E0408`), and must be pure (`E0409`). At construction `ServerCfg.{ host: "ril.dev" }`, explicit fields evaluate left-to-right first, then omitted defaults evaluate in declaration order.

```ril
type WithId<R> = .{ id: int, ..R }
nominal type ServerCfg = .{ host: str, port: int = 8080, var retries: int = 3 }

fn get_id(item: .{ id: int, .. }) -> int { item.id }
let cfg = ServerCfg.{ host: "ril.dev" }
assert(get_id(.{ id: 7, active: true }) == 7 && cfg.port == 8080 && cfg.retries == 3)
assert(get_id(inner(cfg) |> \_ -> .{ id: 1 }) == 1)
-- type BadAliasDef = .{ port: int = 8080 }             -- Error [E0359]: transparent alias forbids field defaults
-- type BadDup = .{ id: int, id: int }                  -- Error [E0210]: duplicate field label
-- type BadOverlap = WithId<.{ id: str }>               -- Error [E0212]: row remainder overlaps 'id'
-- type BadTail = WithId<int>                           -- Error [E0306]: row tail requires a structural record type
-- let bad_extra: .{ id: int } = .{ id: 1, x: 2 }       -- Error [E0302]: unexpected field 'x'
-- let bad_miss: .{ host: str, port: int } = .{ host: "a" } -- Error [E0307]: missing field 'port'
-- let bad_unknown = cfg.email                          -- Error [E0336]: unknown field 'email'
-- let bad_dyn = cfg["host"]                            -- Error [E0324]: dynamic bracket indexing prohibited on records
-- let bad_mode: .{ var x: int } = .{ x: 1 }            -- Error [E0357]: incompatible member mode
-- nominal type BadNested = .{ inner: .{ x: int = 1 } } -- Error [E0359]: field default only on root declaration
-- nominal type BadMutDef = .{ mut items: []int = [] }  -- Error [E0404]: writable field mode forbids default
-- nominal type BadFwd = .{ a: int = b, b: int = 1 }    -- Error [E0408]: forward field reference in default
-- eff Rng { fn next() -> int }
-- nominal type BadImpure = .{ seed: int = Rng::next() }-- Error [E0409]: field default must be pure
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
SumTypeDecl      ::= ( TypeDeclHead | OpaqueTypeHead ) "{" { Newline } [ VariantDeclList ] "}" [ UseCleanupClause ]
VariantDeclList  ::= VariantDeclItem { ( "," | Newline ) VariantDeclItem } [ "," ] { Newline }
VariantDeclItem  ::= VariantSpread | VariantDecl
VariantSpread    ::= ".." TypeReference
VariantDecl      ::= { MetaAttr } PascalCase [ TypeExpression ]
                   | ".."
UseCleanupClause ::= "use" ValueName
```

- **Construction, Sugars & Payload Modes**: Unit variants evaluate directly (`None`, `Pending`; passing an argument such as `Ready ()` fails `E0338`). Payload variants take one space-separated argument (`Ok 42`, `Ok ()`, `Pair (1, 2)`, `Node .{ id: 1 }`); bare payload-variant names have function type `fn(Payload) -> Sum` (`42 |> Ok`). `?T` desugars to `Option<T>` (`Some T`, `None`), and `!<T, E>` desugars to `Result<T, E>` (`Ok T`, `Err E`). Variant payloads attenuate the outer sum's access mode by the payload's own source mode: storing a sum carrying an old `^mut` / `ref` / immutable payload into an exclusive `mut` / `[mut]Sum` receiver fails `E0522` / `E0510` (use `[^mut]Sum` / `[ref]Sum`).
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
let opt: ?int = 99 |> Some
let res: !<int, str> = 42 |> Ok
assert(opt == Some 99 && res == Ok 42)
-- type BadSingleRes = !<int>          -- Error [E0120]: '!<T, E>' requires both Ok and Err type arguments
```

#### Sum Variant Spreading and Subset Conversion

`..SubType` splices another accessible transparent sum's variants into a superset sum (`E0306` on non-sum, `E0308` on sealed/open sum, `E0313` on spread cycles, `E0213` on conflicting payload types for the same variant tag; identical variant tags with definitionally equal payloads deduplicate cleanly). Where `Sup` is also transparent (i.e., non-`opaque`, or inside an `opaque` sum's exact defining scope; sealed outside with `E0308` / `E0301`), this establishes static sum inclusion $Sub \preceq_{\text{sum}} Sup$:

1. **Postfix `?` Automatic Widening**: Inside a function returning `!<T, Sup>`, `sub_res?` widens `Err sub_err` to `Sup` automatically when $Sub \preceq_{\text{sum}} Sup$.
2. **Explicit Widening (`expr as SupType`)**: Re-wraps a `Sub` value into `Sup` when $Sub \preceq_{\text{sum}} Sup$ (`E0301` otherwise).
3. **Pattern Subset Narrowing (`SubType as binder`, `..SubType`)**: Matches any variant belonging to `SubType`.

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
| `ref` / `mut` access with live/mutable payload members | Scoped observation/access bounded by source lifetime; persistent `let ref` (`E0543`) and root `-> ref(src)` (`E0545`) are prohibited; contained return records `&return{ref src}` |

### Nominal, Type Alias, and Opaque Types

Ril defines four `.ril` type declaration forms alongside `.d.ril` opaque host handles:

```ebnf
TypeDecl        ::= TypeDeclHead "=" ( TypeExpression | TypeFunctionExpr )
NominalTypeDecl ::= NominalTypeHead [ "=" TypeExpression ] [ UseCleanupClause ]
OpaqueTypeDecl  ::= OpaqueTypeHead [ "=" TypeExpression ] [ UseCleanupClause ]
TypeDeclHead    ::= { MetaAttr } [ Visibility ] "type" PascalCase [ GenericParams ]
NominalTypeHead ::= { MetaAttr } [ Visibility ] "nominal" "type" PascalCase [ GenericParams ]
OpaqueTypeHead  ::= { MetaAttr } [ Visibility ] "opaque" "type" PascalCase [ GenericParams ]
LocalTypeDecl   ::= TypeDecl | NominalTypeDecl | OpaqueTypeDecl | SumTypeDecl
```

| Form | Declaration | Identity, construction & unwrapping |
| :--- | :--- | :--- |
| Transparent alias | `type Point = .{ x: f64, y: f64 }` | Definitionally equal to its target everywhere (`E0313` on alias cycles; forbids `meta(...)` `E0708` and field defaults `E0359`) |
| Nominal type / marker | `pub nominal type Marker`<br>`pub nominal type UserId = int`<br>`pub nominal type Req = .{ k: str }` | Distinct type everywhere (`E0305`); representation is public. Unit `Marker` is a value; non-record `UserId 42` uses whitespace; nominal record `Req.{ k: "a" }` attaches `.{`. Prelude `inner(w)` unwraps accessible nominal wrappers (`inner(UserId 42) == 42`, `inner(Marker) == ()`) |
| Scope-opaque type | `pub opaque type Token = str` | Interconvertible with its representation inside its exact defining `sub` or root file (`<Token> != <str>` in `Type<...>` and exported signatures); sealed outside, including child/parent `sub`s (`E0301` on type/construction mismatch, `E0308` on field/variant/introspection penetration). Bodyless `.ril` `opaque type` requires a registered built-in/stdlib identity (`E0902`) |
| Sum type | `pub type Res<T, E> { Ok T, Err E }` | Tagged union (`opaque` seals variant construction, subset widening, and pattern matching outside exact defining scope, `E0308`) |
| Foreign opaque handle (`.d.ril`) | `pub opaque type OwnedFd use close` | Exclusive host-managed affine handle (`E0907` on structural penetration, `E0908` on unannotated snapshot/`^mut` signature): forbids `clone` (`E0301`), `derive` (`E0536`), `==` (`E0327`), plain `let`/`var` freezing (`E0535`), `var mut` overwrite (`E0532`), and array/map/set storage (`E0301`, `E0328`); admits `new`, `let mut`, `mut`, `ref`, and `use` |

```ril
pub nominal type Disconnected
pub nominal type Connected
pub nominal type UserId = int
pub nominal type OrgId  = int
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
-- pub type MissingEq .{ id: int }     -- Error [E0124]: missing '=' in type declaration
-- type Cyc = Cyc                      -- Error [E0313]: cyclic transparent type alias
-- Outside Conn's defining scope:
-- let bad_peek = c1.fd                -- Error [E0308]: opaque representation is sealed outside defining scope
```

### Deep Immutability

Plain `let`, `var`, default parameters, and plain collection elements hold **deeply immutable snapshots**: no surviving writable alias (`mut` / `^mut`) and no live `ref` dependency may reach the stored graph (`E0535`). When an immutable value is received for a schema containing `var`/`mut`/`ref` members, those member modes remain inactive on the frozen snapshot (`E0520` on write).

`clone(value)` / `clone(ref live)` deep-copies an ordinary `SharedObject` graph (preserving internal aliasing and cycles) into an isolated `new T`. Every reachable constituent type must be clonable: value roots, callables, and graphs whose types recursively contain `.d.ril` `opaque` handles, `Scope`, `Task`, `Sender` (use `Channel::clone`), `Receiver`, or `Draft` fail `E0301`, and graphs containing live/mutable closure environments fail `E0530`.

```ril
type Cell = .{ var count: int }
let mut live = Cell.{ count: 1 }
-- let bad_snap = live                 -- Error [E0535]: 'live' has surviving write authority
let snap = clone(ref live)             -- OK: isolated snapshot frozen into 'let'
let mut copy = clone(snap)             -- OK: 'clone' returns isolated 'new Cell'
copy.count = 99
assert(live.count == 1 && snap.count == 1 && copy.count == 99)
let ^mut shared = live
let mut holder = .{ ^mut cb: \-> { shared.count += 1; shared.count } }
-- let mut bad_holder = .{ mut cb: \-> { shared.count += 1; shared.count } } -- Error [E0510]: closure retains '^mut' source
assert((holder.cb)() == 2)
-- let _ = clone(ref holder)           -- Error [E0530]: cannot clone structure holding mutable closure authority
```

### Type Identity and Subtyping

Ril has **no implicit numeric widening** and **no structural width subtyping** on closed records (`E0301`). Subtyping $S <: T$ holds only for:
1. Reflexivity / definitional equality ($S \equiv T$, expanding transparent `type A = B` aliases, plus bidirectional `A` $\leftrightarrow$ `Rep` conversion for `.ril` `opaque type A = Rep` inside its exact defining `sub` or root file).
2. Bottom type (`never <: T` for every well-formed `T`).
3. Covariant immutable optionals and results (`?S <: ?T` when $S <: T$; `!<S1, E1> <: !<S2, E2>` when $S_1 <: S_2 \land E_1 <: E_2$; mutable/invariant containers require `S ≡ T`).
4. Callable contract subsumption (`MatchCallable`: contravariant parameter types, covariant return type, identical concrete access modes, and bounded effect/state rows).

### Complete Provenance and Required Annotations

Access modes, origins, state writes, environment captures, and effects are static judgments verified modularly across call boundaries and erased before code generation. Named functions spell their required minimal operational effects (`@Eff`) and non-pure state/provenance clauses (`&mut`, `&^mut`, `&capture`, `&up{...}`, `&return{...}`); anonymous closures infer full contracts automatically.

### Access Mode Inference with via and infer

`via` binds static access-mode parameters over parameter/member schemas; `-> infer T` derives the return mode (`plain`, `ref(...)`, `^mut(...)`, `new`) and `&return{...}` provenance while keeping data type `T` explicit.
- Named callable declarations writing `-> infer T` require an explicit `via` parameter (root `via x: U` or composite `[via]U` / `[K: via V]` / `.{ via f: U }`) in that callable's own parameter list (`E0412`).
- In a `CallableType` parameter (`via cb: fn(...) ... -> infer T` or `cb: fn(via A) ... -> infer T`) or an anonymous closure inside a lexical `via` template, `-> infer T` and `let via` bind to the callable's own `via` or enclosing `via` parameter (`E0412` when no `via` is in scope, including standalone `via`-field types outside `via`/`infer` signatures).

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

`via` in composite parameter schemas (`[via]T`, `[K: via V]`, `.{ via item: T }`) binds an implicit member-mode parameter from the caller's schema. Ordinary access and replacement use the received schema. Concrete member/element modes match supplied modes exactly (`E0357` on mismatch). Qualified `new` reception selects modes for new regions; old-source modes remain fixed.

#### Inference Domains and Contract Completion

A `via x: T` parameter admits modes from `{plain, ref, mut, ^mut, new}` compatible with `T` and all body uses. Writing `via` on a concrete fixed-value scalar (`via n: int`) where only one mode can ever exist fails `E0550`. Inside a `via` function, concrete `&mut` / `&^mut` / `&return` clauses implied solely by `via` instantiations are recorded in the inferred template interface automatically without requiring redundant source spelling on the `via` function header.

#### Preserving Reception and Forwarding

Within a lexical `via` template, `let via y = expr` preserves the exact instantiated access mode and the new-region/contained-source provenance of a `via`-dependent expression (`E0550` if `expr` has a fixed non-dependent mode). A receiver's expected writable mode cannot manufacture construction qualification for an old immutable or `ref` source. Concrete calls to non-`via` parameters still require explicit `mut` / `ref` / `^mut` / `new` argument markers (`E0405`).

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
| Root eligibility (`E0536`, `E0308`) | `base` must be a deeply immutable `SharedObject` (including accessible `nominal` and in-scope `.ril` `opaque` shared objects; sealed `.ril` `opaque` roots fail `E0308`); value types, `.d.ril` `opaque` handles, and live `mut`/`^mut`/`ref` roots fail `E0536` |
| `Draft<T>` path operations | Confined `mut Draft<T>` paths permit `d.field = v` (regardless of `var`), tuple-slot updates `d.0 = v`, `mut` collection operations (`d.tags \|> mut Array::push(...)`), `inner(mut d)` on accessible nominal wrappers, and `match mut d { Tag (mut p) -> ... }` in-place variant payload updates |
| `Draft<T>` confinement (`E0607`) | `Draft<T>` is bound to the recipe activation; draft handles, derived `ref`/`mut` paths, and capturing closures cannot escape the recipe (`E0607`) |
| Inserted values (`E0535`) | Assigned values must be deeply immutable or recipe-local fresh allocations free of external surviving writers (`E0535`) |
| Fixed shape (`E0336`, `E0312`) | Preserves record fields, tuple arity, and active sum tags of `T`; forwards recipe operational effects and external state obligations |

```ril
nominal type Bag = []int
let t2 = (1, "a") |> derive \mut d -> { d.0 = 2 }
let b2 = (Bag [1, 2]) |> derive \mut d -> { inner(mut d) |> mut Array::push(3) }
assert(t2 == (2, "a") && inner(b2) == [1, 2, 3])
```

### Generic Parameters, Defaults, and Value Sorts

Declarations admit rigid type parameters (`T`), compile-time value parameters (`cap: int`), and member-mode parameters (`M: MemberMode`). Type declarations (`type`, `nominal type`, `opaque type`, and `TypeFunctionExpr`) additionally admit trailing default generic arguments (`E0316` if non-trailing, `E0320` on self/forward parameter reference; generic defaults on `fn` or `meta fn` are prohibited with `E0317`).

```ebnf
GenericParams         ::= "<" GenericParamDecl { "," GenericParamDecl } [ "," ] ">"
GenericParamDecl      ::= TypeParamDecl | ConstParamDecl | ModeParamDecl
TypeParamDecl         ::= PascalCase [ TypeConstraint ] [ "=" TypeExpression ]
TypeConstraint        ::= [ ":" TypeSort ] { "|>" PipelineConstraint }
TypeSort              ::= TypeSetSort | "Type" | RecordConstraint
TypeSetSort           ::= TypeSetMember "|" TypeSetMember { "|" TypeSetMember }
TypeSetMember         ::= PrimitiveType | TypeReference | TupleType | ArrayType | MapType | RecordType
PipelineConstraint    ::= QualifiedName [ GenericArgs ]
ConstParamDecl        ::= ValueName ":" TypeExpression { "|>" PipelineConstraint } [ "=" Expression ]
RecordConstraint      ::= ".{" RecordConstraintField { "," RecordConstraintField } "," RecordTail "}"
                        | ".{" RecordTail "}"
RecordConstraintField ::= [ RecordFieldMode ] FieldLabel ":" TypeExpression
ModeParamDecl         ::= PascalCase ":" ModeSortReference [ "=" MemberModeLiteral ]
ModeSortReference     ::= [ "Reflect::" ] "MemberMode"
GenericArgs           ::= "<" [ GenericArg { "," GenericArg } [ "," ] ] ">"
GenericArg            ::= TypeExpression | Expression | MemberModeLiteral
MemberModeLiteral     ::= "let" | "var" [ "mut" | "^mut" | "ref" ] | "mut" | "^mut" | "ref"
```

- **Closed Type Sets (`T: int | f64`, `E0301`, `E0304`, `E0306`, `E0318`)**: Restricts `T` to a finite set of rigid types; every member is checked at the definition site (`E0301`), each call specializes `T` to one rigid type (`E0306` if unspecialized), and `match <T>` covering all set members is exhaustive (`E0304` on redundant `_`). Untagged unions or literal values as storage types fail `E0318`.
- **Pipeline Guards (`T |> Guard<Args>`, `E0301`, `E0306`)**: Evaluates `Guard<T, Args>` with the guarded parameter passed first; `T` satisfies a type-parameter guard iff $T \not\equiv \text{never} \wedge \text{Guard}\langle T, \text{Args} \rangle \equiv T$.
- **Static Value Guards (`cap: int |> Positive`)**: Evaluates `Guard<cap, Args>` after sort checking and static substitution, accepting `<()>`, rejecting `<never>` (`E0323`), and failing `E0306` on any other type token. `Key<T>` (`val |> Key<T>` $\equiv$ `Key<val, T>`) validates static coordinates of `T`.
- **Strict Parameter Sorts (`E0306`, `E0323`, `E0814`, `E0340`, `E0344`)**: Ordinary values/tokens cannot supply type parameters (`E0306`; write `typeof e`). Wrong value sorts fail `E0323`; runtime values in const args fail `E0814`; wrong generic arity fails `E0340`; undetermined type/const parameters fail `E0344`. Type syntax adapts one-way to a declared `Type<T>` const parameter.

```ril
fn add<T: int | f64>(a: T, b: T) -> T { a + b }
assert(add(2, 3) == 5 && add(1.5, 0.5) == 2.0)

type Positive = \n: int -> if n > 0 { <()> } else { <never> }
type AtLeast = \n: int, lo: int -> if n >= lo { <()> } else { <never> }
type Chunk<T = int, cap: int |> Positive |> AtLeast<1> = 64, M: MemberMode = mut> = .{ [M] data: []T }
type DefaultChunk = Chunk<>
type FrozenChunk  = Chunk<int, 1, let>          -- OK: 'let' selects plain immutable member mode
type WrongGuard = \n: int -> <str>
type Guarded<n: int |> WrongGuard> = int
-- type BadGuard = Guarded<1>                  -- Error [E0306]: value guard returns <str>, not <()> or <never>
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
-- type BadEff = @io                   -- Error [E0330]: effect is not a data type
-- type BadState = &mut                -- Error [E0331]: state clause is not a data type
-- type BadVar { Run @io }             -- Error [E0332]: effect suffix on sum variant
-- type BadFld = .{ x: int @io }       -- Error [E0333]: effect suffix on non-callable field
-- type BadBnd<T: @io> = T             -- Error [E0334]: effect bound on generic parameter
-- type BadTFn = \T @io -> <T>         -- Error [E0335]: effect annotation on type function
-- let bad_val: str @io = "hi"         -- Error [E0613]: effect annotation on value binding
```

| Invalid placement | Diagnostic |
| :--- | :---: |
| Bare `@Eff` or open `@` as a `TypeDecl` target | `E0330` |
| Bare `&mut` / `&up` or open `&` as a `TypeDecl` target | `E0331` |
| Effect or state suffix on a sum variant | `E0332` |
| Effect or state suffix directly on a non-callable record/tuple field | `E0333` |
| Effect or state bound on a generic parameter (`<T: @io>`) | `E0334` |
| Effect or state annotation on a `TypeFunctionExpr` (`\T @io -> <T>`) | `E0335` |
| Effect annotation on a value binding or array type (`let x: str @io`) | `E0613` |

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
| `D` | Package (`pkg`) and module scopes, visibility/opacity, type `use` cleanup contracts, primitive/foreign signatures |
| `Delta` | Rigid type, const, member-mode, and record-row parameters |
| `Gamma` | Value bindings, slot/access modes, callable contracts, lexical region tags ($\sigma$) |
| `Phi` | Declared generic constraints and static `match <T>` branch evidence |
| `F` | Origin sets, active construction paths (`new`), aliasing/exclusivity, `Result` inspection obligations |
| `q` | Phase: `TypeEval`, `MetaValue`, or `RunTime` |

### Type Formation and Binding

- **K-TYPE**: Primitives, rigid parameters in `Delta`, well-sorted generic applications, distinct-label records, arity-$0$ or $\ge 2$ immutable-slot tuples, valid-mode collections, complete `CallableType` contracts, `Type<A>`, and forward-evaluated computed types form valid types.
- **K-TYPE-ROW**: `.{ fields L, ..R }` is well-formed iff `R` instantiates to a record row whose labels are disjoint from `L` (`E0306` on non-record `R`, `E0212` on overlapping labels).

### Definitional Equality and Recursive Types

- **K-EQ**: `?T` ≡ `Option<T>`, `!<T, E>` ≡ `Result<T, E>`, and transparent `type A = B` aliases expand directly; cyclic transparent aliases without nominal or sum indirection fail `E0313`. Structural records compare equal up to field reordering when labels, types, and `MemberMode`s match. Nominal, sum, and `opaque` types (both `.ril` and `.d.ril`) compare by declaration identity and static argument equivalence (canonical IEEE bits for `f64` where `-0.0 != 0.0` and NaNs agree; structural value equivalence for collections/records; definitional target identity for `Type<A>`).
- **Opacity Scope**: Inside its exact defining `sub` or root `.ril` file, `opaque type A = Rep` converts bidirectionally with `Rep` across construction, projection, operators, and pattern matching while retaining `A`'s distinct identity in `Type<A>` and exported interfaces; outside that exact scope (including child or parent `sub`s), direct value/construction mismatch fails `E0301` and representation penetration (fields, variants, subset widening, static introspection) fails `E0308`.

### Subtyping, Reception, and Contract Compatibility

- **K-RECV (`Receive`)**: Validates receiving an expression of synthesized mode/origins into a target binding, parameter, element, or return schema:
  - Plain immutable receivers require plain deeply immutable inputs, or a `new` result with freezable new regions and deeply immutable old-source boundaries (`E0535` on surviving writers or `ref` mode/origins).
  - Persistent `mut` bindings, `mut` fields, and `[mut]T` / `[K: mut V]` elements require unshared writable authority or `new` regions free of `^mut` constituents (`E0510` unacknowledged alias, `E0522` container laundering, `E0520` immutable/`ref` source). Temporary `mut` parameters (`fn(mut p: T)`) accept `mut` or `^mut` places under `mut place` / `|> mut` (`E0406` marker mismatch, `E0523`/`E0524` call overlap).
  - Shared `^mut` receivers (`let`/`var ^mut`, `^mut` fields, `[^mut]T` / `[K: ^mut V]` elements) require writable sources (`^mut` acknowledgment on existing roots, `E0510`, or `new` `&up` closures retaining a `^mut` source).
  - `let ref` and `var ref` declarations accept pinned `let mut` origins, non-`var` `ref` handles, or immutable shared objects (`E0531` on `var` / `var ref` roots, `E0543` on unanchored temporaries, `E0604` if not outliving `var ref`). `var ref` reassignments and `ref` member/element slots (`[ref]T`, `[K: ref V]`, `.{ [var] ref f: T }`) require `ref`-mode expressions—existing `ref` bindings/parameters or explicit `ref expr` (`E0357` on bare plain/`mut` values). Writing into an existing mutable heap `ref` slot rejects local live/temporary borrows (`E0531` / `E0604` / `E0607`), while fresh `new` wrappers record `&return{ref x}`.
  - `new` receivers require qualified construction results or `new x` root handoff ending `x` (`E0548`, `E0549`), choosing modes only for new regions while preserving old-source boundaries.
  - Scoped `use [mut] x = expr` anchors `expr` in an implicit block cleanup slot until scope exit, checking `expr` against $\max(M_{\text{body}}, M_{\text{clean}})$ and exposing `ref` (or `mut`) inside the block.

### Bidirectional Expression Checking

- **Synthesis & Checking (`K-EXPR`)**: Operands evaluate and check left-to-right; contextual expected types propagate inward to empty array/map literals (`[]`), anonymous closures (`\x -> ...`), sum constructors (`Ok 1` under `!<int, str>`), and `if`/`match` arms (`E0344` if any required type/const instantiation or monomorphic storage schema remains undetermined).

#### Anonymous Generalization and Fixed Storage

- **K-ANON**: Local `let` bindings of pure anonymous functions generalize unresolved unconstrained parameters and structural row constraints (`let identity = \x -> x`, `let get_id = \r -> r.id`), specializing independently at each call site. When an unannotated closure contains multiple `?` sites over `!<_, E_i>`, its inferred error type selects the unique greatest sum $E_{\max} \in \{E_i\}$ under $\preceq_{\text{sum}}$ (`E0344` if no single member dominates and no contextual `CallableType` supplies the target sum). Mutable storage slots (`var`, array/map elements, record fields) and escaping runtime values require fixed monomorphic schemas (`E0344` if unanchored).

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
  - `TypeEval` and `MetaValue` run under the root step budget (`E0811` exhaustion; `E0830` failed `assert`; `E0831` `panic` or arithmetic defect).
  - Run-time values and storage cannot materialize `Type<T>` tokens (`E0816`). `meta fn` returns, `meta let` constants, and `meta(...)` attributes must be token-free (`E0812` / `E0816`), callable-free (`E0816`), and `use`-resource-free (`E0816`) deeply immutable values (`E0813` on `@Eff` / `&State` on `meta fn`).
  - Direct saturated `meta fn` calls with static arguments (`E0814` on runtime arguments) fold in `RunTime` to deeply immutable snapshots with `new` stripped (`E0520` on `let mut`; use `clone(...)` for a mutable copy). First-class runtime references to a `meta fn` fail `E0810`.
  - `typeof expr` checks `expr` in an isolated shadow of the enclosing scope without evaluating it or folding `meta fn` calls: internal `E0549` and statement `E0720` apply (`expr`'s root `Result` is exempt from `E0720`), while outward `@Eff`, `&State`, `E0527` uses, and caller `E0549` endings are empty. Its result carries the baseline schema without `new` or source authority.

```ril
meta fn build_lookup(scale: int) -> []int {
    [1 * scale, 2 * scale, 3 * scale]
}
-- meta let BAD_FN = \x: int -> x      -- Error [E0816]: callable cannot escape 'meta let'

fn sample(i: int) -> int {
    let table = build_lookup(10)       -- OK: compile-time folded immutable []int snapshot
    -- let mut bad = build_lookup(10)  -- Error [E0520]: 'meta fn' fold strips 'new' freshness
    -- let fn_ref = build_lookup       -- Error [E0810]: 'meta fn' is not a runtime function value
    table[i]
}
type SampleOut = typeof(sample(0))     -- int (unevaluated)
-- fn ghost(mut xs: []int) -> int { let _: typeof({ Array::push(mut xs, 1); 0 }) = 0; len(ref xs) } -- Error [E0527]
assert(sample(1) == 20 && <SampleOut> == <int>)
```

### Semantic Interfaces and Diagnostic Boundaries

- **K-IFACE**: Compiled module interfaces retain normalized parameter/return schemas, parameter labels and defaults, `via` mode correlations, `use` cleanup contracts, `Sendable` / `SharedObject` representation facts across `opaque` boundaries, operational-effect footprints, and minimal provenance relations. Return metadata maps new/old regions to nested member/element paths and branch alternatives, preserved by generic substitution, aliases, callable storage, and module export.

---

## Declarations and Bindings

```ebnf
LetDecl               ::= [ Visibility ] "let" ( ScreamingSnakeCase | UnmodifiedPattern ) [ ":" TypeExpression ] "=" Expression
LetMutDecl            ::= "let" "mut" UnmodifiedPattern [ ":" TypeExpression ] "=" Expression
SharedMutDecl         ::= ( "let" | "var" ) "^mut" ( ValueName | Wildcard ) [ ":" TypeExpression ] "=" Expression
VarDecl               ::= "var" ( ValueName | Wildcard ) [ ":" TypeExpression ] "=" Expression
VarMutDecl            ::= "var" "mut" ( ValueName | Wildcard ) [ ":" TypeExpression ] "=" Expression
LetRefDecl            ::= "let" "ref" UnmodifiedPattern [ ":" TypeExpression ] "=" Expression
VarRefDecl            ::= "var" "ref" ( ValueName | Wildcard ) [ ":" TypeExpression ] "=" Expression
ModePreservingBinding ::= "let" "via" UnmodifiedPattern [ ":" TypeExpression ] "=" Expression
UseResourceDecl       ::= "use" [ "mut" ] ( ValueName | Wildcard ) [ ":" TypeExpression ] "=" Expression
```

### Binding Modes and Storage Matrix

| Form | Slot rebinding | Interior access | Required source |
| :--- | :---: | :--- | :--- |
| `let x = e` | Fixed (`E0501`) | Deeply immutable (`E0520`) | Snapshot free of live writers/refs (`E0535`) |
| `var x = e` | Reassignable | Deeply immutable (`E0520`) | Snapshot free of live writers/refs (`E0535`) |
| `let mut x = e` | Pinned (`E0502`) | Writable; existing root sharing requires acknowledgment | Qualified `new` / constructor or unshared writable source; contained shared sources remain shared |
| `var mut x = e` | Reassignable | Writable; existing root sharing requires acknowledgment | Non-foreign qualified `new` / constructor (`E0532` on `.d.ril` handles; cannot anchor `let ref`, `E0531`) |
| `let ^mut x = e` | Pinned (`E0502`) | Shared writable | Existing writable handle (`^mut` marker) or `new` `&up` closure retaining a `^mut` source |
| `var ^mut x = e` | Reassignable | Shared writable | Writable handle (`^mut` marker on replacement) |
| `let ref x = e` | Pinned (`E0502`) | Read-only live view (`E0520`) | Pinned `let mut`, non-`var` `ref` handle, or immutable shared object (`E0531` on `var` / `var ref`, `E0543`) |
| `var ref x = e` | Reassignable | Read-only live view (`E0520`) | Eligible origin outliving `x` (`ref expr` or `ref` handle on replacement; `E0357`, `E0531`, `E0543`, `E0604`) |
| `use [mut] x = e` | Pinned & confined (`E0502`, `E0604`) | `ref` (`use x`) or `mut` (`use mut x`) | Satisfies $\max(M_{\text{body}}, M_{\text{clean}})$ for type's `use <fn>` cleanup (`E0541`) |

#### Reachable Authority Use

Every declared mutable slot, writable handle, shared-authority marker, and mutable parameter must have a statically reachable use after literal dead-branch pruning (`E0527: UnusedAuthorityError`; code after `never` transfers, literal `if false` / `while false`, `typeof(...)`, signature guards, and ungrounded recursive self-forwarding do not count, whereas `meta let` platform branches remain checked):

| Declared authority | Required reachable use (`E0527` when absent) |
| :--- | :--- |
| `var x` / `var ref x` | Reachable slot replacement (`x = ...` or compound assignment) |
| `let mut x` / `mut p` parameter | Reachable interior write, `mut`/`^mut` forwarding to a grounded writer, or `new` handoff |
| `use mut x` | Reachable interior write or `mut` borrow forwarding inside the block (`use mut _` always fails `E0527`; write `use x` or `use _`) |
| `var mut x` | Both reachable slot replacement and reachable writable/consuming use |
| `let ^mut x` | Both shared writable reception and reachable writable use |
| `var ^mut x` | Reachable slot replacement, shared writable reception, and reachable writable use |
| `^mut p` parameter / handler binder | Surviving writable retention beyond temporary call/arm duration (root `-> ^mut(p)`, `&return{^mut p}`, `&^mut` store, or `&capture`; mutating `p` alone without retention fails `E0527`) |
| `^mut expr` sharing marker | Target receiver requires shared writable authority (`let ref r = ^mut src` fails `E0527`) |
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

A pinned `let mut` initialized by construction, `clone`, or a qualified `new` result retains construction qualification while its new regions have no independent surviving external aliases. Contained old sources keep their own provenance. `new x` preserves identity, ends `x` and dependent paths (`E0549`), and leaves independent old-source paths valid.

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

let snapshot = clone(ref b2)
-- let mut bad = new snapshot          -- Error [E0548]: immutable source
let ref view = b2
-- let mut bad_ref = new view          -- Error [E0548]: read-only source
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

var ref cur_view = fixed_doc
cur_view = ref draft                   -- OK: 'var ref' reassignment takes explicit 'ref'
-- cur_view = fixed_doc                -- Error [E0357]: 'var ref' slot requires 'ref' expression
-- let ref bad_vref = cur_view         -- Error [E0531]: reassignable 'var ref' cannot anchor 'let ref'

let mut docs: []Doc = [fixed_doc]      -- OK: plain 'let' snapshots use '[]Doc'
Array::push(mut docs, fixed_doc)
-- let mut bad_views: [ref]Doc = [fixed_doc] -- Error [E0357]: plain element does not match '[ref]Doc'
let mut views = [ref fixed_doc]        -- OK: explicit 'ref' synthesizes '[ref]Doc'
Array::push(mut views, ref fixed_doc)
-- Array::push(mut views, reader)      -- Error [E0531]: mutable heap 'ref' slot rejects local live borrow
```

### Scoped Resource Bindings

`use [mut] x = expr` anchors a non-escaping resource in a block slot for the remainder of the enclosing block whose static type `T` declares an accessible `use <fn_name>` cleanup contract (`E0541` otherwise).

```ril
pub opaque type DbConn = .{ var open: bool, mut log: []str } use close

pub fn close(new c: DbConn) @io -> () {
    let mut owned = new c
    owned.open = false
    println("closed")
}

pub fn acquire() -> new DbConn {
    DbConn.{ open: true, log: [] }
}

fn run_query() @io -> !<int, str> {
    use ro = acquire()                          -- Exposes 'ref' in body; still runs close(new ro) on exit
    assert(ro.open)
    use mut conn = acquire()
    conn.log |> mut Array::push("SELECT 1")
    -- close(new conn)                          -- Error [E0604]: scoped source path cannot end early
    -- use mut idle = acquire()                 -- Error [E0527]: 'use mut' has no body write; write 'use'
    -- use bad_plain = 42                       -- Error [E0541]: 'int' declares no 'use' cleanup contract
    -- use var bad = acquire()                  -- Error [E0532]: 'use' resource bindings cannot use 'var'
    -- return conn                              -- Error [E0604]: 'use' binding cannot escape block
    Ok 1                                        -- Invokes close(new conn), then close(new ro)
}
-- pub opaque type BadFiber = .{ fd: int } use fiber_close
-- pub fn fiber_close(new _c: BadFiber) @fiber -> () {} -- Error [E0616]: '@fiber' prohibited on 'use' cleanup
-- fn missing_io() -> () { use _ = acquire() }          -- Error [E0612]: unhandled @io from close
```

| `use` & `use <fn>` rule | Requirement |
| :--- | :--- |
| Eligible declarations (`E0541`) | `use fn_name` (attached on the same line as the type end) is permitted on `SharedObject` `OpaqueTypeDecl` / `NominalTypeDecl` / `SumTypeDecl` and `.d.ril` `DeclOpaqueType` / `DeclNominalType` / `DeclSumType`. `fn_name` resolves in the same scope to `fn(ref Self) [@Eff] -> ()`, `fn(mut Self) [@Eff] &mut -> ()`, or `fn(new Self) [@Eff] -> ()` without `&^mut` or `&capture` (`E0541`), satisfying `E0910` visibility |
| Slot reception & body mode | `use x = expr` exposes read-only `ref` access in the block (`use _` retains an anonymous slot); `use mut x = expr` exposes `mut` access (`E0527` requires a body write). `expr` is checked against $\max(M_{\text{body}}, M_{\text{clean}})$ under $\text{\texttt{ref}} < \text{\texttt{mut}} < \text{\texttt{new}}$ (`E0548` / `E0520` when insufficient) |
| Cleanup effects (`E0616`, `E0612`) | Synchronous `@io` and user `fn` effects are permitted on `fn_name` and charged to the `use` site (`E0612`); `@fiber` is prohibited (`E0616: ScopedCleanupEffectError`). Enclosing `with Eff::op() -> ...` handlers declared **above** `use` outlive it and discharge its cleanup `@Eff`; handlers declared **below** exit earlier and cannot discharge it |
| Confinement & LIFO (`E0532`, `E0604`) | Forbids `use var` (`E0532`), `^mut` sharing, local rebinding, early `new x` handoff, return escape, and closure/fiber capture (`E0604` / `E0601`). Runs once per initialized binding in reverse declaration order on block exit, `return`, `break`, `continue`, `?`, panic unwinding, and unshielded `@fiber` cancellation; a secondary panic inside cleanup during active unwinding terminates the OS process immediately |

### Declaration Metadata Attributes

Compile-time `meta(expr1, expr2)` attributes attach deeply immutable constant values (`E0814` on non-static expressions, `E0812`/`E0816` on tokens/callables) to `nominal type`, `opaque type`, sum, `sub`, nominal/opaque root record-field, variant, effect, or function declarations (`E0708` on transparent `type` aliases, structural record fields, `use` imports/bindings, or local `let`/`var` statements).

```ebnf
MetaAttr    ::= "meta" "(" MetaArgList ")"
MetaArgList ::= Expression { "," Expression } [ "," ]
```

```ril
pub nominal type Route = str
pub nominal type Role  = str

meta(Route "/users", Role "admin")
pub nominal type CreateUserReq = .{
    meta(Role "pii")
    email: str,
}
-- meta(Route "/x") type BadAlias = int              -- Error [E0708]: 'meta(...)' prohibited on transparent alias
-- type BadFieldMeta = .{ meta(Role "pii") id: int } -- Error [E0708]: structural record field forbids 'meta(...)'
```

### External Interface Declarations

External host contracts reside in `.d.ril` files (`DeclFile`). `.d.ril` files contain declarations without bodies (`E0901` on function bodies, initializers, field defaults, `=` representation bodies on `opaque type`, or `opaque` on sum/nominal/alias declarations; standard `.ril` functions or bodyless `opaque type` declarations fail `E0902` unless matching a registered language/stdlib built-in).

```ebnf
DeclUnitItem    ::= UseDecl | DeclSub | DeclFunction | DeclType | DeclEffect | DeclLet
DeclSub         ::= { MetaAttr } [ Visibility ] "sub" PascalCase
                    "{" { DeclUnitItem Separator } [ DeclUnitItem ] "}"
DeclFunction    ::= { MetaAttr } [ Visibility ] "fn" ValueName [ GenericParams ]
                    "(" [ ParameterList ] ")" ReturnSpec
DeclType        ::= DeclSumType | DeclNominalType | DeclTypeAlias | DeclOpaqueType
DeclTypeHead    ::= { MetaAttr } [ Visibility ] "type" PascalCase [ GenericParams ]
DeclNominalHead ::= { MetaAttr } [ Visibility ] "nominal" "type" PascalCase [ GenericParams ]
DeclSumType     ::= DeclTypeHead "{" { Newline } [ VariantDeclList ] "}" [ UseCleanupClause ]
DeclNominalType ::= DeclNominalHead [ UseCleanupClause ]
DeclTypeAlias   ::= DeclTypeHead "=" TypeExpression
DeclOpaqueType  ::= { MetaAttr } [ Visibility ] "opaque" "type" PascalCase [ GenericParams ]
                    [ UseCleanupClause ]
DeclEffect      ::= { MetaAttr } [ Visibility ] "eff" PascalCase [ GenericParams ]
                    "{" { Newline } [ EffectMemberList ] "}"
DeclLet         ::= [ Visibility ] "let" ScreamingSnakeCase ":" TypeExpression
```

| `.d.ril` contract rule | Requirement |
| :--- | :--- |
| Field & representation sealing (`E0907`) | Foreign opaque handles (`DeclOpaqueType`) and host-managed nominal shapes (`DeclNominalType`) cannot be constructed directly, unwrapped via `inner`, or penetrated via field/pattern/introspection access in `.ril` (`E0907`, taking precedence over `E0308`) |
| Supported authority (`E0908`) | Foreign signatures cannot use `^mut`, `&^mut`, `&capture`, or `via`/`infer`, and cannot pass or return a `DeclOpaqueType` as an unannotated plain snapshot (`ref`, `mut`, or `new` parameter and `new` return required, `E0908`) |
| `opaque type` handles | `pub opaque type OwnedFd use close` models exclusive host-managed affine handles: forbids `clone` (`E0301`), `derive` (`E0536`), `==` (`E0327`), plain `let`/`var` freezing (`E0535`), `var mut` overwrite (`E0532`), `^mut` (`E0908`/`E0510`), and `[M]OwnedFd` / `[K: M OwnedFd]` / `Set<OwnedFd>` collections (`E0301`, `E0328`); supports `new` creation/consumption (`E0549` after `new fd`), `let mut`, `mut`, `ref`, and `use` |
| Pure `DeclLet` & `@io` isolation (`E0906`, `E0608`) | `DeclLet` admits pure immutable value/data constants only (`DeclOpaqueType` or mutable types in `DeclLet` fail `E0906`); host-stateful foreign functions must declare `@io` so `absorb_panic` (`E0608`) modularly isolates host side effects |

```ril
-- File: sys/posix.d.ril
pub opaque type OwnedFd use close

pub fn open_path(path: str) @io -> new !<OwnedFd, str>
pub fn read_bytes(ref fd: OwnedFd, max_len: int) @io -> !<bytes, str>
pub fn close(new fd: OwnedFd) @io -> ()
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
FallbackExpr             ::= LogicalOrExpr [ "??" ( FallbackExpr | AnonFnExpr | AccessorExpr | ControlTransfer ) ]
LogicalOrExpr            ::= LogicalAndExpr { "||" LogicalAndExpr }
LogicalAndExpr           ::= ComparisonExpr { "&&" ComparisonExpr }
ComparisonExpr           ::= PipelineExpr [ RelOperator PipelineExpr ]
RelOperator              ::= "==" | "!=" | "<" | "<=" | ">" | ">="
PipelineExpr             ::= RangeExpr { PipelineStep }
PipelineStep             ::= "|>" [ ArgumentMode ] ( AnonFnExpr | AccessorExpr | PipelineTarget [ TrailingClosure ] ) [ "?" ]
                           | "as" TypeReference
ForIterable              ::= RangeExpr { "|>" [ ArgumentMode ] ( AnonFnExpr | AccessorExpr | PipelineTarget [ TrailingClosure ] ) [ "?" ] }
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
                           | ObserveExpr
                           | SharingExpr
                           | ConstructorExpr
                           | PostfixExpr
ConstructionTransferExpr ::= "new" ValueName
ObserveExpr              ::= "ref" PostfixExpr
SharingExpr              ::= "^mut" PostfixExpr
ConstructorExpr          ::= ConstructorPath [ "new" | "ref" | "^mut" ] ConstructorArg
ConstructorPath          ::= { "Super" "::" } { PathSegment "::" } PascalCase [ GenericArgs ]
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
PipelineTarget           ::= AtomExpr
                           | PipelineTarget "(" [ ArgumentList ] ")"
                           | PipelineTarget ( "." | "?." ) ( FieldLabel | TupleIndex | "(" Expression ")" )
                           | PipelineTarget [ "?" ] "[" ( Expression | SliceRangeExpr ) "]"
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
RecordValueField         ::= [ MemberMode ] FieldLabel [ ":" Expression ]
TupleExpr                ::= "(" Expression "," Expression { "," Expression } [ "," ] ")"
ArrayExpr                ::= "[" [ Expression { "," Expression } [ "," ] ] "]"
MapExpr                  ::= "[" ":" "]"
                           | "[" MapEntry { "," MapEntry } [ "," ] "]"
MapEntry                 ::= Expression ":" Expression
```

| Precedence (high → low) | Operators / forms | Associativity |
| :---: | :--- | :---: |
| 1 | `.` `?.` `f(...)` `f \...` `a[i]` `a?[i]` `?` `Type.{...}` `::` | Left |
| 2 | Unary `-` `!` `~` `ref e` `^mut e` `new x`, space constructor `Tag arg` | Right |
| 3 | `*` `/` `%` | Left |
| 4 | `+` `-` | Left |
| 5 | `<<` `>>` | Left |
| 6 | `&` | Left |
| 7 | `^` | Left |
| 8 | `\|` | Left |
| 9 | `..` `..=` | Non-associative |
| 10 | `\|>` `\|> ref` `\|> mut` `\|> ^mut` `\|> new` (with optional step `?`), `e as SupType` | Left |
| 11 | `==` `!=` `<` `<=` `>` `>=` | Non-associative |
| 12 | `&&` | Left (short-circuit) |
| 13 | `\|\|` | Left (short-circuit) |
| 14 | `??` | Right (short-circuit) |
| 15 | `let ... else` | Non-associative |
| 16 | `=` `+=` `-=` `*=` `/=` `%=` `&=` `\|=` `^=` `<<=` `>>=` | Non-associative (`E0701`) |
| 17 | `where` (`BlockWhereClause`) | Non-associative |

- **Lexical Adjacency, Argument Markers & Space Construction (`E0125`, `E0406`)**: Function calls attach `(` (`parse(s)`), array/map indexing attaches `[` (`xs[0]`), and all named record constructions attach `.{` (`User.{ id: 1 }`). At the top level of a call `Argument`, leading `mut`, `ref`, `^mut`, or `new` always parses as the call's `ArgumentMode` marker (`E0406` if mismatched against a plain parameter). Sum variants and non-record nominal constructors require whitespace before their payload (`Ok 42`, `Ok ()`, `Some .{ x: 1 }`, `Some [1, 2]`, `Ok (-1)`). Bare `Block` `{...}` and bare `AnonFnExpr` `\...` are excluded from `ConstructorArg`, so `if opt == None { ... }` and `call(None) \-> ...` parse unambiguously.
- **Expression Holes (`...`, `E0360`)**: `...` has type `never`, satisfies any expected type and access mode during partial checking, and suppresses cascading `E0527` / `E0549` diagnostics along paths ending in `...`, while failing complete builds with `E0360: UnfinishedExpressionHoleError`.

```ril
type Buf = .{ var len: int }
-- fn draft_fill(mut buf: Buf) &mut -> int {
--     ...                                -- Error [E0360]: unfinished expression hole in complete build
-- }
```

### Arithmetic, Bitwise, Relational, and Logical Operators

- **Arithmetic (`+`, `-`, `*`, `/`, `%`, unary `-`)**: Defined exclusively on `(int, int) -> int` and `(f64, f64) -> f64` (`E0327` on `str`, `bytes`, or `bool`; strings combine via interpolation `"{a}{b}"`). Integer `/` truncates toward zero and `%` satisfies `(a / b) * b + (a % b) == a`. Syntactic literal `0` divisors fail `E0361` at check time; non-literal `/ 0` or `% 0` panics at evaluation time (`E0831` in static evaluation; `Numeric::checked_div` and `Numeric::checked_rem` return `?int`). Explicit numeric conversions use `Numeric::to_f64(n: int) -> f64`, `Numeric::convert<int>(x: f64) -> ?int`, and `Numeric::trunc(x: f64) -> ?int`.
- **Bitwise & Shifts (`~`, `&`, `|`, `^`, `<<`, `>>`)**: Defined exclusively on `int` (`E0327` elsewhere) using infinite-width two's-complement semantics (`~x == -x - 1`, `x >> k` arithmetic floor shift). Syntactic negative literal shift counts (`-k`) fail `E0361`; non-literal `k < 0` panics at evaluation time (`E0831` in static evaluation).
- **Equality & Ordering (`==`, `!=`, `<`, `<=`, `>`, `>=`)**:
  - `==` / `!=` require same-type operands (`E0301`, `E0305` on distinct nominals) whose type recursively excludes callables, `.d.ril` `opaque` handles, `Scope`, `Task`, `Sender`, `Receiver`, and `Draft` (`E0327`; `f64` follows IEEE-754 where `NaN != NaN` and `-0.0 == 0.0`, and `?T == None` / `!= None` tests the option tag even when `T` lacks equality). Map keys and `Set` elements additionally forbid `f64`, extensible `{ .. }` sums, and mutable member modes (`E0328`).
  - Static type-token comparison is an exception: operands of `Type<A>` and `Type<B>` may have different metatypes. `<A> == <B>` holds iff `A` and `B` are definitionally equal; `!=` is its complement. The represented types need not support value equality.
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

### Indexing, Slicing, and Static Coordinate Projection

- **Indexing & Slicing (`xs[i]`, `xs?[i]`, `xs[a..b]`, `xs[a..=b]`)**:
  - Arrays `[M]T` accept `int` element indices (`xs[i]` panics out of bounds; `xs?[i] -> ?T` returns `None` out of bounds). Single-element bracket indexing on `str` or `bytes` is rejected (`E0352`; use `String::at` / `Bytes::at`), and dynamic bracket indexing on records fails `E0324`.
  - Sequence slicing `s[a..b]` / `s[a..=b]` (and safe `s?[a..b]`) produces a fresh array on `[M]T` (preserving element modes; binding directly to `let ref` fails `E0543`), a Unicode-scalar sub-string on `str`, and a byte sub-sequence on `bytes`.
  - Maps `[K: M V]` require safe lookup `m?[k] -> ?V` for reads (`E0352` on `m[k]` reads or `m[k] += v`); direct slot assignment `m[k] = v` inserts or updates key `k`. On live `[M]T` and `[K: M V]` containers, `xs[i]`, `xs?[i]`, and `m?[k]` expose scoped element projections bounded by the container; mutating or resizing the container while any `ref`/`mut` element projection is live or during `for` iteration fails `E0537` / `E0526`.
- **Tuple & Static Coordinate Projection (`t.0`, `r.(key)`)**: `t.0` projects tuple elements (`E0312` out of bounds; `E0337` on sums, records, collections, or primitives); `r.(key)` projects an accessible record field or tuple slot using a compile-time `meta` coordinate `key` validated by `Key<T>`.

```ril
let xs = [10, 20, 30, 40]
let text = "hello, 世界"
assert(xs[1..3] == [20, 30] && xs?[9] == None && text[0..5] == "hello")
let m = ["port": 8080]
assert(m?["port"] == Some 8080 && m?["host"] == None)
-- let _ = m["port"]                    -- Error [E0352]: map read requires 'm?["port"]'
-- let _ = "abc"[0]                     -- Error [E0352]: 'str' element access uses 'String::at'
-- let _ = (Some 1).0                   -- Error [E0337]: sum has no '.0' projection
type Cell = .{ var v: int }
let mut cells = [Cell.{ v: 1 }]
let ref elem = cells[0]
-- cells |> mut Array::push(Cell.{ v: 2 }) -- Error [E0537]: mutating array while 'elem' is live
assert(elem.v == 1)
cells |> mut Array::push(Cell.{ v: 2 }) -- OK: 'elem' last use has ended
```

### Text and Byte Operations

Strings combine via interpolation `"{left}{right}"` or `String::join`. Prelude modules `String` and `Bytes` provide dual-phase text, diagnostic formatting, and byte operations:
- `String::inspect<T>(via value: T) -> str`: pure dual-phase diagnostic formatter accepting plain values/snapshots or `ref` shared-object views (`E0401` on `ref` value types; `mut`/`^mut`/`new` markers rejected). Formats primitives, escaped `str`/`bytes` literals, tuples, collections, and transparent records/nominals/sums structurally (rendering runtime reference cycles as `"..."`), and formats sealed `opaque` types outside their defining scope, `.d.ril` `opaque` handles, callables, and runtime concurrency/draft handles as `"<TypeName>"` (or `"<fn>"`).
- `String::starts_with(text: str, prefix: str) -> bool`, `String::ends_with(text: str, suffix: str) -> bool`
- `String::at(text: str, index: int) -> ?int`, `String::scalars(text: str) -> new []int`, `String::from_scalars(via values: []int) -> ?str`
- `String::encode_utf8(text: str) -> bytes`, `String::decode_utf8(data: bytes) -> ?str` (`None` on ill-formed UTF-8)
- `Bytes::at(data: bytes, index: int) -> ?int`, `Bytes::to_array(data: bytes) -> new []int`, `Bytes::from_array(via values: []int) -> ?bytes` (`None` if any integer lies outside `0..=255`)

```ril
type Pair = .{ var id: int, label: str }
let mut p = Pair.{ id: 6, label: "ok" }
p.id = 7
assert(String::inspect(ref p) == `.{ id: 7, label: "ok" }` && String::inspect(Some 3) == "Some 3")
assert(String::starts_with("src/lexer.ril", "src/") && String::ends_with("src/lexer.ril", ".ril"))
assert(Bytes::from_array([65, 66]) == Some bytes"AB" && Bytes::from_array([256]) == None)
assert(String::decode_utf8(String::encode_utf8("Ril")) == Some "Ril")
assert(String::decode_utf8(bytes"\xC0\xAF") == None)
```

### Pipeline and Fallible Operators

- **Mode-Aware Pipelines (`x |> [mode] f(a) [\...] [?]` / `x |> [mode] f [\...] [?]`)**: Evaluates `x` first, then callee `f` and remaining arguments left-to-right, passing `x` as the first argument under `[mode]` (`E0338` if `f` is non-callable); an optional trailing `?` propagates `Result` / `Option` on that step's call result (`x |> f(a)?` ≡ `(f(x, a))?`):

| Pipeline form | Equivalent call | Left-operand requirement |
| :--- | :--- | :--- |
| `x \|> f` / `x \|> f(a)` | `f(x)` / `f(x, a)` | `Expression` (immutable snapshot, value copy, or lexical `via`) |
| `x \|> ref f` / `x \|> ref f(a)` | `f(ref x)` / `f(ref x, a)` | `Expression` (scoped read-only `ref` access) |
| `x \|> mut f` / `x \|> mut f(a)` | `f(mut x)` / `f(mut x, a)` | `AssignTarget` (`E0410` on non-place rvalues) |
| `x \|> ^mut f` / `x \|> ^mut f(a)` | `f(^mut x)` / `f(^mut x, a)` | `AssignTarget` (`E0410` on non-place rvalues) |
| `x \|> new f` / `x \|> new f(a)` | `f(new x)` / `f(new x, a)` | `Expression` (ends `x` before evaluating `f` or `a`, `E0549`) |

- **Error/Option Propagation (`expr?`)**: Valid inside an ordinary function or closure body (`E0205` at module/`sub` top-level); preserves the selected `Ok`/`Some` payload's own mode, construction qualification, and contained sources. A new sum wrapper does not make an old payload new:
  - On `!<T, E>` (`E0712` on non-`Result`/non-`Option`): unwraps `Ok v` to `v`, or early-returns `Err e` (widening `e` when $E \preceq_{\text{sum}} E_{\text{ret}}$; incompatible enclosing return types fail `E0713`).
  - On `?T`: unwraps `Some v` to `v`, or early-returns `None` when the enclosing callable returns `?U` (`E0713` otherwise).
- **Right-Associative Fallback (`opt ?? b ?? c` / `res ?? \err -> fallback`)**:
  - `?T ?? T`: evaluates right operand lazily only on `None` (`E0714` on invalid left operand).
  - `!<T, E> ?? fn(E) @... -> T`: invokes the handler closure with `e` on `Err e`, discharging `Result`'s `E0720` obligation (`E0711` if right operand is not `fn(E) -> T`; outer `break`/`continue`/`return` across a fallback or closure boundary fails `E0707`/`E0710`).
- **Safe Navigation (`opt?.field`, `opt?[idx]`)**:
  - `?.` requires `?T` (`E0715`); `?[` accepts direct or `?`-wrapped `[M]T`, `[K: M V]`, `str` (slice), and `bytes` (slice) (`E0352` / `E0715`).
  - Within an unparenthesized postfix chain, `?.` / `?[` short-circuits `None` to the end of the chain and lifts the result once to `?R` without double-wrapping `?R`.

```ril
type Config = .{ host: ?str }
type Route  = .{ pair: (str, int) }
fn resolve_host(cfg: ?Config) -> str { cfg?.host ?? "localhost" }
fn parse_pos(s: str) -> !<int, str> { if s == "80" { Ok 80 } else { Err "bad" } }
fn check_port(p: int) -> !<int, str> { if p > 0 { Ok p } else { Err "zero" } }
fn load_port(raw: str) -> !<int, str> { Ok (raw |> parse_pos? |> check_port?) }

let maybe_r: ?Route = Some Route.{ pair: ("db", 5432) }
assert(maybe_r?.pair.1 == Some 5432 && [10, 20]?[1] == Some 20)
-- let _ = (maybe_r?.pair).1            -- Error [E0337]: parentheses end '?.' chain, yielding '?(str, int)'

let mut buf = [1, 2]
buf |> mut Array::push(3)
assert(buf |> ref len == 3 && resolve_host(None) == "localhost")
assert(load_port("80") == Ok 80 && load_port("x") == Err "bad")
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
- **Assignments (`target = expr`, `target += expr`, ...)**: Assignment is a `()`-typed expression and does not chain (`a = b = 1` fails `E0701`). `target` must be a `var` variable, a `var` record field on a `mut`/`^mut` path, an element of a `mut`/`^mut` array/map, or a field/tuple slot on a confined `mut Draft<T>` path (`E0501` on `let` or plain record fields, `E0502` on pinned `let mut`/`let ref`, `E0503` on rvalues or non-draft tuple slots; map compound assignment `m[k] += v` fails `E0352`). Compound assignments evaluate `target`'s receiver/index expression exactly once.

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
                    | ModePreservingBinding | UseResourceDecl
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
  - All declarations in `BlockWhereClause` form one mutually recursive scope hoisted across the entire enclosing block. Value bindings (`let`, `var`, `use`) enter scope strictly after their initializer completes; invoking a `where` helper before an outer local variable it captures has been initialized fails `E0207`.
  - Local nominal, `opaque`, and sum types declared in `SignatureWhereClause` or `BlockWhereClause` cannot escape in the enclosing callable's signature or outer mutable storage (`E0315`; transparent `type` aliases in `SignatureWhereClause` expand cleanly). Block-local `eff` effects must be handled inside their declaring block (`E0618`). Visibility modifiers (`pub`, `pub(pkg)`) are prohibited inside blocks and `where` clauses (`E0703` / `E0120`).

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
IfExpr          ::= "if" ( Expression | "let" [ "mut" | "ref" | "^mut" ] UnmodifiedPattern "=" Expression ) Block
                    [ "else" ( IfExpr | Block ) ]
WhileExpr       ::= "while" ( Expression | "let" [ "mut" | "ref" | "^mut" ] UnmodifiedPattern "=" Expression ) Block
ForExpr         ::= "for" [ "ref" | "mut" | "^mut" | "new" ] ForIterable "as" Pattern Block
ControlTransfer ::= "return" [ Expression ]
                  | "break"
                  | "continue"
```

- **Conditionals**: `if cond { a } else { b }` requires `cond: bool` (`E0350`) and a common join type across normal branches (`E0351`). Without `else`, the `then` block must have type `()` (or `never`). `if let [mode] pat = expr { ... } [else { ... }]` matches refutable `pat` against `expr`.
- **Loops & Transfers (`E0355`, `E0526`, `E0707`)**:
  - `while cond { body }` (`cond: bool`, `E0350`) and `while let [mode] pat = expr { body }` check `body` against `()`. When `cond` is syntactically the bare boolean literal `true` (`while true { ... }`) and `body` contains no `break` targeting that `while` (ignoring `break`s captured by nested inner loops), the expression has no normal continuation and synthesizes `never`; all other `while` expressions synthesize `()`.
  - `for [mode] iter as pat { body }` iterates over `[]T`, `[K: V]` (yielding `(K, V)`), `Set<T>`, or integer ranges `a..b` / `a..=b` (`E0355` on non-iterable values), checking `body` against `()` and synthesizing `()`. `pat` must be irrefutable (`E0345`). Default `for` / `for ref` borrows live collections read-only; `for mut` / `for ^mut` exposes element write access while forbidding structural resize/reallocation of the iterated collection (`E0526`); `for new` consumes a `new` collection and yields `new` elements.
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
GuardedLetStmt ::= "let" [ "mut" | "ref" | "^mut" ] UnmodifiedPattern "=" Expression "else" Block
```

`let Pat = expr else { ... }` matches refutable `Pat`; on mismatch, the `else` block executes and **must** diverge (`never` via `return`, `break`, `continue`, `panic`, or `?`; normal completion of `else` fails `E0321`). Guarded `let ... else` is explicitly exempt from `E0309`, permitting zero-binder assertions such as `let Ok () = check() else { return Err "denied" }`.

Plain `let Pat = expr` without `else` requires an irrefutable pattern (`E0345`) that introduces at least one variable binder (except explicit `let _ = expr`; vacuous `let () = f()` or `let Marker = m` fails `E0309`).

```ril
fn validate(header: ?str, check: fn(str) -> !<(), str>) -> !<str, str> {
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
MatchExpr            ::= "match" Expression "{" { Newline } [ MatchArm { ( "," | Newline ) MatchArm } [ "," ] { Newline } ] "}"
MatchArm             ::= Pattern [ "if" Expression ] "->" ( Expression | ControlTransfer )
Pattern              ::= OrPattern
OrPattern            ::= SinglePattern { "|" SinglePattern }
UnmodifiedPattern    ::= UnmodifiedSingle { "|" UnmodifiedSingle }
SinglePattern        ::= UnmodifiedSingle
                       | BindingModifier ValueName
UnmodifiedSingle     ::= SubsetPattern
                       | ConstructorPattern
                       | PatternAtom
                       | RangePattern
                       | TypePattern
SubsetPattern        ::= TypeReference "as" ( [ BindingModifier ] ValueName | Wildcard )
                       | ".." TypeReference
ConstructorPattern   ::= ConstructorPath ( PatternAtom | BindingModifier ValueName )
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
| Symmetry with construction | Tight `Type.{ a, b }` unpacks named records; space-separated `Some x`, `Some mut c`, `Ok ()`, `Pair (a, b)`, `UserId id` unpack variants and non-record nominals (`E0314` on tuple arity mismatch; `E0349` on arbitrary expressions or `{expr}` interpolations in patterns) |
| Or-patterns & unique binders (`E0346`, `E0347`) | Alternatives `P1 \| P2` must bind the exact same set of names with identical types and modes (`E0346`); duplicate binder names in one conjunction fail `E0347` |
| Range patterns (`E0348`) | `lo..hi` / `lo..=hi` require non-empty integer intervals (`lo < hi` for `..`, `lo <= hi` for `..=`, `E0348`) |
| `str[...]` non-overlapping slices (`E0349`) | At most one `..` / `..rest` segment (`E0349` on multiple `..`, empty literal segments, or `{expr}` interpolations); matches `s` iff `s` starts with concatenated prefix literals, ends with concatenated suffix literals, and `len(s) >= len(prefix) + len(suffix)` |
| Exhaustiveness & reachability (`E0303`, `E0304`) | `match` must cover all possible inhabitants (`E0303`; `if guard` arms do not count toward coverage). Unreachable arms (including shadowed subset/variant arms) fail `E0304` |
| Pattern reception (`E0402`, `E0521`, `E0551`) | Value-type binders forbid `ref`/`mut`/`^mut` (`E0402`); requesting `mut`/`^mut` from an immutable/`ref` subject fails `E0521`; requesting mutable/incompatible decomposition on an immutable tuple or fixed-mode sub-slot fails `E0551` |

```ril
fn classify_packet(raw: str) -> str {
    match raw {
        str["{{", ..body, "}}"] -> "json:{body}", -- Requires len(raw) >= 2; `{` does NOT match!
        str["GET ", ..path]     -> "get:{path}",
        _                       -> "other",
        -- "dead"               -> "never",       -- Error [E0304]: unreachable match arm
    }
    -- match true { true -> 1 }                   -- Error [E0303]: non-exhaustive match (missing 'false')
    -- match (1, 2) { (x, 2) | (1, y) -> 0, _ -> 1 } -- Error [E0346]: or-pattern binder mismatch
    -- let (dup, dup) = (1, 2)                    -- Error [E0347]: duplicate binder 'dup'
    -- match 5 { 10..5 -> 0, _ -> 1 }             -- Error [E0348]: empty range pattern
    -- match raw { str[..a, ..b] -> a, _ -> "" }  -- Error [E0349]: multiple '..' in str[...]
}
assert(classify_packet(`{ok}`) == "json:ok" && classify_packet(`{`) == "other")
let snap_rec = .{ fixed: [1, 2] }
-- let .{ mut fixed } = snap_rec                  -- Error [E0521]: cannot bind 'mut' from immutable record
-- let (mut bad_slot, _) = ([1], [2])             -- Error [E0551]: tuple slot cannot decompose as 'mut'
```

### Flow-Sensitive Type Narrowing

Conditions using `== None`, `!= None`, `!`, `&&`, `||`, and early-diverging `if` / `while` guards refine the static type of `?T` bindings and field paths in-place across dominance regions without introducing new variable names:

| Narrowing rule | Requirement |
| :--- | :--- |
| Optional unboxing | `x != None` (or `!(x == None)`) narrows `x: ?T` by one optional layer to `T`; `if x == None { return ... }` narrows sequential successor flow to `T` |
| Contradictory test (`E0311`) | Testing `== None` or `!= None` when disjoint from the active optional state of a single-layer `?T` fails `E0311: ContradictoryNarrowingError` (nested `??T` unboxes one layer at a time) |
| Write invalidation (`E0310`) | Immutable `let` paths through immutable fields narrow without depth limit. Reassigning `var`, writing an overlapping mutable path, or calling an `@Eff` whose enclosing `with` arm writes that path resets the refinement (`E0310: InvalidatedNarrowingAccessError`) |
| Unknown alias / handler hazard (`E0533`) | Across an open-state (`&`, `@&`), open-effect (`@`), or unhandled `@Eff` call—or a `^mut` write not proved disjoint from a live path (`ref` does not prove independence; `clone` into `let` does)—reading the prior live refinement fails `E0533: AliasedNarrowingHazardError` |

```ril
type Cell = .{ var val: ?int }

fn check_narrowing(mut cell: Cell, hook: fn() & -> (), eff_cb: fn() @ -> (), nested: ??int) &mut -> int {
    var local: ?int = Some 10
    if local == None {
        -- if local != None { return 0 }        -- Error [E0311]: contradictory 'None' narrowing
        return 0
    }
    let ok = local + 1                          -- Sequential flow narrowed 'local' to 'int'
    local = None
    -- let _ = local + 1                        -- Error [E0310]: 'local' narrowing invalidated by assignment

    if nested != None {
        if nested == None { return ok }         -- OK: 'nested: ??int' unboxed one layer to '?int'
    }
    if cell.val != None {
        hook()
        -- let _ = cell.val + 1                 -- Error [E0533]: open '&' call may alias live 'cell.val'
    }
    if cell.val != None {
        eff_cb()
        -- let _ = cell.val + 1                 -- Error [E0533]: open '@' call may invoke stateful handler
    }
    let snap = clone(ref cell)
    cell.val = None
    if snap.val != None { ok + snap.val } else { ok } -- OK: immutable 'snap' survives 'hook()' and 'cell' writes
}
```

---

## Functions, Closures, and Callables

### Named Function Declarations and Contrast Matrix

```ebnf
FunctionDecl         ::= { MetaAttr } [ Visibility ] "fn" ValueName [ GenericParams ]
                         "(" [ ParameterList ] ")" ReturnSpec
                         [ [ SignatureWhereClause ] Block ]
SignatureWhereClause ::= "where" SignatureWhereList
SignatureWhereList   ::= SignatureWhereItem { Separator SignatureWhereItem } [ Separator ]
SignatureWhereItem   ::= LocalTypeDecl | FunctionDecl | MetaFnDecl
ParameterList        ::= Parameter { "," Parameter } [ "," ]
Parameter            ::= RegularParam | MetaParam
RegularParam         ::= [ ParameterMode ] ( ValueName | Wildcard )
                         [ ":" TypeExpression ] { ContractGuard }
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
| Ordinary `fn` | `fn f(...) [@Eff] [&State] -> T { ... }` | Run-time (pure core operations dual-phase) | Explicit `@Eff` and minimal `&State` required on named definitions (`E0510`, `E0529`, `E0612`) |
| Compile-time `meta fn` | `meta fn f(...) -> T { ... }` | Static (`TypeEval` / `MetaValue` + saturated compile-time fold in `RunTime`) | Pure only (`E0813`); result token-, callable-, and resource-free (`E0812`, `E0816`) |
| Type function | `type F = \T -> <...>` | Static (`TypeEval`) | Pure only (`E0335`); returns single `Type<U>` token |
| Built-in bodyless `fn` | Bodyless `fn` in prelude `.ril` | Per primitive contract | Must match registered primitive module, name, and signature (`E0902`, `E0909`) |
| Foreign `.d.ril` `fn` | Bodyless `pub fn` in `.d.ril` | Run-time | Body prohibited (`E0901`); stateful host calls declare `@io` |

#### Dual-Tier Where Invariants

| Tier rule | Requirement |
| :--- | :--- |
| `SignatureWhereClause` (`E0704`, `E0120`) | Braceless `where` list (`where { ... }` and `pub`/`pub(pkg)` on `where` items fail `E0120`) permitted on bodied `fn` / `meta fn` declarations and terminated by the body's opening `{`. Admits `LocalTypeDecl` (`type`), `FunctionDecl` (`fn`), and `MetaFnDecl` (`meta fn`); declaring `eff` or `sub` fails `E0704: InvalidSignatureWhereItemError` (value bindings fail `E0702`). Visible across the function signature (`PipelineConstraint`s, `ContractGuard`s, types) and body |
| Signature confinement (`E0706`, `E0315`) | Types and guards referenced in the signature must be declared in `SignatureWhereClause` or an enclosing scope (`E0706` on `BlockWhereClause` references; non-transparent local `nominal`/`opaque`/sum declarations in `SignatureWhereClause` cannot escape in the signature, `E0315`) |
| Downward isolation & uniqueness (`E0705`, `E0203`) | `SignatureWhereClause` items cannot reference `BlockWhereClause` items (`E0705: DownwardScopeReferenceError`), whereas `BlockWhereClause` may reference `SignatureWhereClause`. Duplicate names across both tiers fail `E0203` |

```ril
pub fn map_fallible<T, R, E>(xs: []T, step: StepFn<T, R, E>) @io -> !<[]R, E>
where
    type StepFn<In, Out, Err> = fn(In) @io -> !<Out, Err>
{
    let mut out: []R = []
    for xs as item { Array::push(mut out, step(item)?) }
    Ok out
where
    fn _helper_tag() -> int { 1 }
}

-- fn bad_braced(x: int) -> int where { type T = int } { x }        -- Error [E0120]: 'where' clauses do not use '{ ... }'
-- fn bad_sig_eff(x: int) -> int where eff E { fn op() -> () } { x } -- Error [E0704]: 'eff' prohibited in signature 'where'
-- fn bad_down() -> Wrap where type Wrap = .{ s: Inner } { Wrap.{ s: .{ n: 0 } } where type Inner = .{ n: int } } -- Error [E0705]
-- fn bad_sig_ref(cb: Cb) -> () { cb() where type Cb = fn() -> () }  -- Error [E0706]: signature references block 'where'
```

#### Signature Value Contracts

`ContractGuard` (`|> [ref] guard(args)`) attaches declarative fallible entry and exit contracts to `RegularParam` and declaration `ReturnSpec` (`FunctionDecl`, `MetaFnDecl`, `DeclFunction`):

| Contract rule | Requirement |
| :--- | :--- |
| Parameter type omission (`E0544`) | A `RegularParam` or `MetaParam` with at least one `ContractGuard` / `PipelineConstraint` (or `=` default on `MetaParam`) may omit `: TypeExpression`, inferring its type from the first guard/default (`E0544` if omitted without a guard/default; `E0344` if undetermined) |
| Pure fallible guard (`E0409`, `E0712`, `E0713`) | Guards must be pure (`E0409` on `@Eff` or mutable/capturing state) and return `!<(), E>` or `?()` (`E0712`) compatible under `?` with the enclosing function's `!<T, E_out>` or `?T` return type (`E0713`) |
| Evaluation & `|> ref` (`E0549`, `E0527`) | Arguments and defaults bind left-to-right first; parameter guards then run in declaration order via `(p |> [ref] guard(args))?`. On `Ok v` / `Some v` return (`Err` / `None` bypasses exit guards), return guards run via `(v |> [ref] guard(args))?`. `|> ref` preserves `new` qualification on `v`; reading a consumed `new` parameter in a return guard fails `E0549`, and guards alone do not satisfy `E0527` |

```ril
pub type Span = .{ lo: int, hi: int }
pub type SpanErr { Inverted, Empty }

pub fn make_span(lo |> ordered(hi), hi: int) -> !<Span, SpanErr> |> non_empty
where
    fn ordered(lo: int, hi: int) -> !<(), SpanErr> {
        if lo <= hi { Ok () } else { Err SpanErr::Inverted }
    }
    fn non_empty(s: Span) -> !<(), SpanErr> {
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
CallableAnnot       ::= "@&"
                      | "@" [ ClosedCallableState ]
                      | EffectAnnot [ CallableStateAnnot ]
                      | CallableStateAnnot
CallableStateAnnot  ::= "&" | ClosedCallableState
ClosedCallableState ::= CallableStateClause { CallableStateClause }
CallableStateClause ::= "&up" | "&up{" "ref" "}" | StateClause
```

#### Mandatory Contract Inference and Completion

The compiler infers complete operational effects and provenance for every callable body:
- Named `fn` declarations must spell exact unhandled operational `@Eff` (`E0612`), minimal concrete state obligations (`&mut`, `&^mut`, `&capture`, `&up{...}`, `&return{...}` — `E0510` when missing, `E0529` when excessive), and non-plain return modes (`new`, `ref(x)`, `^mut(x)` — `E0544` / `E0528`), except where `via` / `infer` encapsulates mode-dependent obligations.
- Anonymous closures `\... -> ...` infer their exact contract automatically; optional written `@Eff` / `&State` / `: Type` annotations constrain inference.

#### Closed and Open Callable Rows

| Callable annotation | Operational effects | State & provenance |
| :--- | :--- | :--- |
| *(omitted)* | Closed empty | Closed pure |
| `@io` | Closed `{io}` | Closed pure |
| `&up{ref}` | Closed empty | Read-only captured closure environment (invocable via plain/`ref` handle) |
| `&up` | Closed empty | Mutable/abstract captured closure environment (invocation requires `mut` or `^mut` handle, `E0520`) |
| `@` | Open effect row | Closed pure (live caller refinements still guard against handler writes, `E0533`) |
| `&` | Closed empty | Open state/provenance row |
| `@&` | Open effect row | Open state/provenance row |

Open markers `@`, `&`, and `@&` are valid only on `CallableType` parameters/fields (`E0547` on named or anonymous definitions).

#### Callable Contract Matching

Under `MatchCallable`, a callable value of actual contract $C_{\text{act}}$ satisfies expected `CallableType` $C_{\text{exp}}$ (`E0534` on contract/return-mode mismatch, `E0407` on parameter mode mismatch) iff:
1. Parameter count matches (`E0314`), parameter types satisfy contravariance, return type satisfies covariance, concrete parameter modes match (`E0407`; `mut` and `^mut` definitions still satisfy `E0527`), and return modes/sources satisfy $C_{\text{exp}}$ (`E0534`).
2. Every operational effect in $C_{\text{act}}$ appears in $C_{\text{exp}}$ (or is covered by an `@SupEff` spread in $C_{\text{exp}}$, unless $C_{\text{exp}}$ is effect-open via `@` or `@&`).
3. Every non-pure state/capture obligation in $C_{\text{act}}$ is permitted by $C_{\text{exp}}$ (`&up{ref}` admits pure/read-only observer closures callable via `ref`; `&up` admits mutable closure environments whose invocation requires a caller-side `mut` or `^mut` handle and charges `&mut` when the callable is a formal parameter; `&` / `@&` opens state obligations). Pure module constants, pure immutable captures, and pure stateless lexical `fn` handlers reduce to empty state; return-source relations remain checked.

```ril
type Cell = .{ var v: int }
type Obs  = fn() &up{ref} -> int
type Step = fn() &up -> int

fn read_obs(ref f: Obs) -> int { f() }         -- OK: '&up{ref}' is read-only
fn run_step(mut f: Step) &mut -> int { f() }   -- OK: '&up' invoked through 'mut' handle
-- fn bad_step(ref f: Step) -> int { f() }     -- Error [E0520]: '&up' requires 'mut' or '^mut' receiver
-- pub fn len(x: int) -> int                   -- Error [E0909]: built-in signature mismatch in prelude
-- fn bad_open() @ -> () {}                    -- Error [E0547]: open '@' row prohibited on named 'fn'
-- fn bad_ret(ref a: []int) -> []int { a }     -- Error [E0544]: missing 'ref(a)' return mode annotation
-- let pure_cb: fn() -> () = \-> println("hi") -- Error [E0534]: '@io' incompatible with pure 'fn() -> ()'
-- let mode_cb: fn([]int) -> () = \mut xs: []int -> Array::push(mut xs, 1) -- Error [E0407]: mode 'mut' vs plain
-- let idle_cb = \mut _xs: []int -> ()         -- Error [E0527]: wildcard does not waive 'mut' use
```

### Return Construction, Access Modes, and Sources

| Return form | Meaning & static check |
| :--- | :--- |
| `-> T` | Deeply immutable snapshot or value copy (`E0528` / `E0535` if live or writable) |
| `-> new T` | New or construction-qualified root whose new regions have no independent surviving external aliases (`E0546` otherwise); the receiver selects legal modes for new regions while preserving contained old sources |
| `-> ref(x \| y) T` | Read-only view rooted in formal `x` or `y`'s call-entry graph (`E0545` if rooted in a local or temporary sum-subset wrapper) |
| `-> ^mut(x \| y) T` | Shared writable handle rooted in `^mut` formal `x` or `y`'s call-entry graph (`E0545` if temporary `mut`; root retention needs no duplicate `&^mut`, `E0529`) |
| `&return{x, ref y, ^mut z}` | Records contained old immutable, live read-only, and shared writable object sources, respectively; normalized metadata associates each source with its possible return paths |

`new` reception selects modes for new regions. Named definitions declare every contained old object source in `&return{...}` (`E0510` if omitted); with none, the result is a complete new graph. `&return{x}` requires a deeply immutable object source (`E0545` otherwise). A non-`via` `new x: T` parameter cannot supply old-source boundaries to a `-> new R` result (`E0548` at call sites when `x` carries old-source boundaries; forward arbitrary contained sources via `fn f<T>(via x: T) -> infer R`). Value copies and ordinary immutable `-> T` returns need no construction-source clause.

Sources are tracked through arbitrary nesting, cycles, and aliases. Projection, pattern decomposition, `inner`, `?`, and sum re-wrapping preserve the selected region's own qualification. An external path back into a new region invalidates construction qualification (`E0546`); strengthening a returned old source fails `E0528`.

```ril
type Node = .{ var val: int }

fn pick_ref(cond: bool, ref a: Node, ref b: Node) -> ref(a | b) Node {
    if cond { a } else { b }
}

fn make_nodes() -> new []Node {
    [Node.{ val: 1 }, Node.{ val: 2 }]
}

fn make_staged() -> new []Node {
    let mut xs: []Node = [Node.{ val: 1 }]
    Array::push(mut xs, Node.{ val: 2 })
    -- xs[0].val = 3                         -- Error [E0520]: current element path is immutable
    xs
}

fn edit_factory(factory: fn() -> new []Node) -> int {
    let mut xs: [mut]Node = factory()         -- OK: the public new contract survives callable storage
    xs[0].val += 1
    xs[0].val
}

fn test_returns() -> () {
    let snap: []Node = make_nodes()            -- Receiver freezes graph as immutable []Node
    let mut edit: [mut]Node = make_nodes()     -- Receiver adopts fresh graph as [mut]Node
    edit[0].val = 10
    let mut shared: [^mut]Node = make_nodes()
    shared[0].val += 1
    assert(snap[0].val == 1 && edit[0].val == 10)
    assert(edit_factory(make_staged) == 2)
}
test_returns()
-- fn bad_wrap(n: Node) -> new []Node { [n] }    -- Error [E0510]: missing old-source boundary '&return{n}'
-- fn bad_src(mut a: Node) &mut -> ^mut(a) Node { a.val += 1; a } -- Error [E0545] / [E0528]
-- fn bad_new(ref a: Node) -> new Node { a }     -- Error [E0546]: 'ref' is not fresh 'new'
```

```ril
type Cell = .{ var value: int }
type Shelf = .{ mut rows: [^mut]Cell }

fn shared_shelf(^mut cell: Cell) &^mut &return{^mut cell} -> new Shelf {
    Shelf.{ rows: [^mut cell] }
}
type WrongShelf = .{ mut rows: [mut]Cell }
-- fn bad_shelf(^mut cell: Cell) &^mut &return{^mut cell} -> new WrongShelf {
--     WrongShelf.{ rows: [^mut cell] }       -- Error [E0357]: ^mut element requires [^mut]Cell
-- }
fn wrap_snapshot(cell: Cell) &return{cell} -> new []Cell { [cell] }
fn wrap_view(ref cell: Cell) &return{ref cell} -> new [ref]Cell { [cell] }
fn wrap_option(cell: Cell) &return{cell} -> new ?Cell { Some cell }
fn id_fresh(new xs: []Cell) -> new []Cell { new xs }
-- let bad_factory: fn(Cell) -> new []Cell = wrap_snapshot -- Error [E0534]: old return source cannot be erased

fn test_contained_sources() -> () {
    let mut cell = Cell.{ value: 0 }
    let mut shelf = shared_shelf(^mut cell)
    shelf.rows[0].value += 1
    let mut next = new shelf
    next.rows[0].value += 1
    assert(cell.value == 2)                  -- Independent old source remains valid and shared
    -- shelf.rows                           -- Error [E0549]: dependent old path ended
    -- let frozen = shared_shelf(^mut cell)  -- Error [E0535]: surviving external writer
    -- let mut bad_view: [mut]Cell = wrap_view(ref cell) -- Error [E0522]: old read-only element

    let snapshot = Cell.{ value: 5 }
    let wrapped = wrap_snapshot(snapshot)    -- OK: every old boundary is deeply immutable
    -- let _ = id_fresh(new wrap_snapshot(snapshot)) -- Error [E0548]: non-'via' '-> new' rejects contained old sources
    -- let mut bad: [mut]Cell = wrap_snapshot(snapshot) -- Error [E0522]: old element cannot gain writes
    let mut copied: [mut]Cell = clone(wrapped)
    copied[0].value += 1
    assert(snapshot.value == 5 && len(id_fresh(new [Cell.{ value: 9 }])) == 1 && copied[0].value == 6)
}
fn read_wrapped(cell: Cell) -> ?int {
    let payload = wrap_option(cell)?         -- Old immutable payload, despite the new Some wrapper
    -- let mut bad = wrap_option(cell)?      -- Error [E0520]: payload itself is not new
    Some payload.value
}
test_contained_sources()
```

### Parameter Modes, Caller Obligations, and Defaults

Parameters forbid `var` (`E0403`; copy into a local `var` if slot replacement is needed). Concrete calls spell explicit argument mode markers (`E0405` if omitted, `E0406` if mismatched, `E0410` if `mut`/`^mut` targets a non-addressable expression):

| Formal parameter | Call-site marker | Authority & obligation |
| :--- | :---: | :--- |
| `x: T` | `expr` or `\|>` | Deeply immutable snapshot or value copy (`E0535` on live writer) |
| `ref x: T` | `ref expr` or `\|> ref` | Scoped read-only access to a shared-object source (`E0401` on value type `T`) |
| `mut x: T` | `mut place` or `\|> mut` | Temporary write access for the call (accepts `mut` or `^mut` places); requires reachable write (`E0527`, `&mut`) and source-overlap checks (`E0523`, `E0524`), and grants no retained writer |
| `^mut x: T` | `^mut place` or `\|> ^mut` | Shared writable handle; requires reachable retention beyond temporary call access (`E0527`; `&^mut` beyond root return) |
| `new x: T` | `new expr` or `\|> new` | Receives a construction-qualified result (`E0548` on an unqualified root, or when a non-`via` `-> new` callee would erase `expr`'s contained old sources; ends `expr` with `E0549`; `E0411` on plain value types) |
| `via x: T` | Mode-dependent | Instantiates static mode template from caller's supplied mode |

```ril
fn bump_node(mut n: Node) &mut -> () { n.val += 1 }
fn consume_node(new n: Node) -> int { n.val }

fn test_params() -> () {
    let mut n0 = Node.{ val: 5 }
    bump_node(mut n0)
    let mut s0 = Node.{ val: 1 }
    let ^mut sh = s0
    bump_node(mut sh)                   -- OK: temporary 'mut' call accepts '^mut' place
    assert(s0.val == 2)
    -- bump_node(n0)                    -- Error [E0405]: missing 'mut' marker at call site
    -- bump_node(ref n0)                -- Error [E0406]: argument mode 'ref' does not match 'mut'
    -- bump_node(mut Node.{ val: 1 })   -- Error [E0410]: 'mut' requires an addressable writable place
    -- bump_node(mut n0, 1)             -- Error [E0314]: arity mismatch (expected 1, got 2)
    assert(consume_node(new n0) == 6)    -- OK: the completed mutable call did not retain an alias
    -- let _ = n0.val                   -- Error [E0549]: old source path ended
}
test_params()
-- fn bad_var(var x: int) -> () { x = 1 }     -- Error [E0403]: 'var' parameter prohibited
-- fn bad_new_val(new x: int) -> int { x }    -- Error [E0411]: 'new' prohibited on value type 'int'
```

#### Default Parameters and Named Arguments

| Default & label rule | Requirement |
| :--- | :--- |
| Permitted default modes (`E0404`) | Plain, `ref`, and `meta` parameters on `FunctionDecl`, `MetaFnDecl`, and `AnonFnExpr` may declare `= default_expr`; defaults on `mut`, `^mut`, `new`, or `via` parameters fail `E0404: MutableParameterDefaultProhibitedError` |
| Scope & purity (`E0408`, `E0409`, `E0910`) | Defaults may reference earlier plain immutable or `meta` parameters in declaration order (`ref b: T = a` may also alias an earlier `ref a: T`; self/forward references fail `E0408`, and `@Eff`, reading live `ref` fields, referencing `mut`/`^mut`/`new` parameters, or mutable/foreign state fails `E0409`). Exported callables require referenced module bindings to satisfy `E0910`; publishing a default closure capturing an earlier parameter charges `&capture` at the caller (`E0510`) |
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
-- fn bad_io_def(s: str = { println("x"); "a" }) @io -> str { s }          -- Error [E0409]
```

### Anonymous Functions, Trailing Closures, and Projection Accessors

```ebnf
AnonFnExpr    ::= "\" [ AnonParams ] [ EffectAnnot ] [ StateAnnot ] "->" AnonFnBody
AnonFnBody    ::= Block | Expression
AnonParams    ::= AnonParam { "," AnonParam } [ "," ]
AnonParam     ::= MetaParam
                | [ ParameterMode ] UnmodifiedPattern [ ":" TypeExpression ] [ "=" Expression ]
AccessorExpr  ::= "\" AccessorNav AccessorField { AccessorNav AccessorField }
AccessorNav   ::= "." | "?."
AccessorField ::= FieldLabel | TupleIndex
```

- **Closure Body Termination & Trailing Closures**: When `{` immediately follows `->`, `AnonFnBody` parses as a self-delimited `Block` ending at its matching `}` (non-block bodies parse as `Expression`). A `CallExpr` or `PipelineStep` may pass its final callable argument as a trailing `AnonFnExpr` or `AccessorExpr` directly after `(...)`—or omit `()` when no other explicit arguments remain (`absorb_panic \-> { ... }`, `Fiber::scope \mut s -> { ... }`). Postfix `?` and outer `|>` steps attach directly after a block-bodied trailing closure.
- **Shorthand Projection Accessors (`\.field`, `\.0`, `\?.field`)**: Desugar to unary pure closures (`\x -> x.field`, `\x -> x.0`, `\x -> x?.field`) over accessible records and tuples (`E0336` on unknown field, `E0312` on out-of-bounds tuple index, `E0337` on sums, collections, or primitives). Any `?.` segment lifts the result to `?T`.

```ril
type Dept = .{ name: str, code: (str, int) }
type Org  = .{ title: str, dept: ?Dept }

fn with_tx<T>(mut log: []str, body: fn(mut []str) @& -> !<T, str>) &mut -> !<T, str> {
    Array::push(mut log, "begin")
    let out = body(mut log)?
    Array::push(mut log, "commit")
    Ok out
}

fn test_closures_and_accessors() -> !<int, str> {
    let orgs = [
        Org.{ title: "Core", dept: Some Dept.{ name: "Infra", code: ("INF", 10) } },
        Org.{ title: "Labs", dept: None },
    ]
    assert((orgs |> Array::map \.title) == ["Core", "Labs"])
    assert((orgs |> Array::map \.dept?.code.1) == [Some 10, None])
    assert(([1, 2, 3] |> Array::map \x -> { x * 2 } |> Array::filter \x -> { x > 2 }) == [4, 6])

    let mut log: []str = []
    let code = log |> mut with_tx \mut entries -> {
        Array::push(mut entries, "insert")
        Ok 200
    }?
    assert(log == ["begin", "insert", "commit"])
    Ok code
}
assert(test_closures_and_accessors() == Ok 200)
```

### Closures and Lexical Environments

Closures infer captures from body uses while preserving each retained source's concrete mode and provenance. Returning or storing a newly created closure that captures any enclosing runtime local/parameter or stateful lexical handler requires `&capture` on the enclosing named `fn` (`E0510`; pure immutable captures still match pure `fn(...) -> ...` targets, whereas live `ref` observer closures match `&up{ref}` and mutable closures match `&up`):

```ril
type CounterCell = .{ var value: int }
type Step = fn() &up -> int

fn make_adder(k: int) &capture -> fn(int) -> int { \x -> x + k }

fn make_counter(^mut cell: CounterCell) &capture &^mut &return{^mut cell} -> new Step {
    \-> {
        cell.value += 1
        cell.value
    }
}

fn test_counter() -> () {
    let add5 = make_adder(5)
    let mut c = CounterCell.{ value: 0 }
    let ^mut step = make_counter(^mut c)
    assert(add5(3) == 8 && step() == 1 && step() == 2 && c.value == 2)
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
StateMode             ::= "var" [ "mut" | "^mut" | "ref" ]
                        | "mut" | "^mut" | "ref"
ReturnDependencyGroup ::= "&return{" ReturnDependencyList "}"
ReturnDependencyList  ::= ReturnDependency { "," ReturnDependency } [ "," ]
ReturnDependency      ::= [ "ref" | "^mut" ] QualifiedName
```

### Local State Discharge, Parameter Mutation, and Sharing

- **Local Discharge**: Writes and `^mut` sharing confined to non-escaping local `var` / `let mut` allocations—and writes confined to the consumed `new` regions of a `new` parameter—discharge locally; the function remains outwardly pure.
- **`&mut`**: Required on named functions that may mutate caller-surviving writable state: a `mut` parameter, a `^mut` parameter, or a `^mut` constituent reachable inside a `new` parameter (`E0510`).
- **`&^mut`**: Required when a `^mut` parameter (or locally allocated shared root) is retained into another parameter, escaping closure environment, or escaping non-root structure (`E0510`; root `-> ^mut(x) T` already accounts for its own return retention).
- **`&capture`**: Required when a named `fn` returns or stores a newly created closure environment capturing any enclosing runtime local/parameter or stateful lexical handler (`E0510`; pure immutable captures match pure `fn(...) -> ...` targets, while module/`sub` constants need zero `&capture`).
- **Contained Immutable Sources**: `&return{x}` adds no state effect and remains part of the return contract.
- **Minimal Annotations (`E0529: ExcessiveStateAnnotationError`)**: Named `fn` declarations must not spell `&mut`, `&^mut`, `&capture`, `&up{...}`, or `&return{...}` clauses that are not actually exercised by the body (`E0529`, including redundant `&^mut` alongside bare root `-> ^mut(x) T`).

```ril
fn reset_owned(new c: Node) -> int {
    let mut o = new c
    o.val = 0                              -- OK: write to consumed 'new' region discharges locally
    o.val
}
fn bump_shelf(new s: .{ mut rows: [^mut]Node }) &mut -> () {
    let mut o = new s
    o.rows[0].val += 1                     -- OK: mutates caller-surviving '^mut' constituent
}
assert(reset_owned(new Node.{ val: 9 }) == 0)
-- fn excess_new(new c: Node) &mut -> int { let mut o = new c; o.val = 0; o.val } -- Error [E0529]
-- fn excess_mut(ref c: Node) &mut -> int { c.val }                               -- Error [E0529]
-- fn dup_share(^mut c: Node) &^mut -> ^mut(c) Node { c }                         -- Error [E0529]
```

### State Groups and Captured Layers

Block-local named `fn` declarations in `BlockWhereClause` that access enclosing local bindings spell `&up{...}` listing the captured outer bindings (`&up{limit}` for plain/`var` read, `&up{var acc}` for `var` reassignment, `&up{ref view}`, `&up{mut buf}`, `&up{^mut shared}`; malformed groups fail `E0538`, unused items fail `E0529`). Module-level and `sub`-level functions never carry `&up{...}` because module/`sub` top-level forbids mutable or live state (`E0906`) and reading pure `let` / `meta let` constants requires **no** state annotation.

```ril
let GLOBAL_FACTOR = 3                  -- Pure module constant

fn scale_all(xs: []int, offset: int) -> []int {
    var total = 0
    let mut out: []int = []
    for xs as x {
        let scaled = transform(x)
        add_total(scaled)
        Array::push(mut out, scaled)
    }
    assert(total == 17)
    out
where
    fn transform(x: int) &up{offset} -> int {
        x * GLOBAL_FACTOR + offset     -- GLOBAL_FACTOR needs no '&up'; outer local 'offset' uses '&up{offset}'
    }
    fn add_total(n: int) &up{var total} -> () {
        total += n                     -- Reassigning outer 'var' spells '&up{var total}'
    }
    -- fn bad_up(x: int) &up{ghost} -> int { x }  -- Error [E0538]: unknown outer source 'ghost' in '&up{...}'
    -- fn idle_up(x: int) &up{offset} -> int { x } -- Error [E0529]: excessive '&up{offset}' not read by body
}
assert(scale_all([1, 2], 4) == [7, 10])
```

### Exclusivity and Anti-Laundering Matrix

At every call and assignment, Ril checks potentially overlapping mutable/live origin sets (immutable snapshots carry zero mutable/live origins). Concrete access modes match exactly; `^mut` arguments and stored elements require `^mut` receivers. Source-overlap checking does not relax mode matching.

| Violation | Diagnostic |
| :--- | :---: |
| Writing through plain immutable or `ref` access, or binding immutable/`ref` data as `mut`/`^mut` | `E0520` |
| Destructuring pattern requesting `mut`/`^mut` from an immutable/`ref` subject or immutable field | `E0521` |
| Upgrading old immutable/`ref`/`^mut` container or sum constituents to exclusive `[mut]`/`mut` modes | `E0522` |
| Overlapping `mut` with `mut`, `^mut`, `new` (carrying `^mut` sources), or an active `with` write loan | `E0523` |
| Overlapping `mut` with `ref`, plain observation, `new` (carrying `ref` sources), or an active `with` loan | `E0524` |
| Mutating a collection during `for` iteration (directly or via an active `with` handler) | `E0526` |
| Returning `mut` / `^mut` / `new` authority from immutable/`ref` or temporary `mut` sources | `E0528` |

```ril
type Box = .{ var n: int }
fn swap_add(mut a: Box, mut b: Box) &mut -> () { a.n += b.n; b.n += 1 }
fn observe_mut(mut a: Box, ref b: Box) &mut -> int { a.n += 1; b.n }
fn take_shared(mut a: Box, new xs: [^mut]Box) &mut -> int {
    let mut s = new xs
    a.n += 1
    s[0].n += a.n
    s[0].n
}

fn test_exclusivity() -> () {
    let mut x = Box.{ n: 1 }
    x.n += 1
    -- swap_add(mut x, mut x)              -- Error [E0523]: overlapping mut-mut origins
    -- let _ = take_shared(mut x, new [^mut x]) -- Error [E0523]: 'mut' overlaps 'new' carrying '^mut x'
    -- let _ = observe_mut(mut x, ref x)   -- Error [E0524]: overlapping mut-ref hazard
    -- let mut bad_elems: [mut]Box = [Box.{ n: 1 }] |> \xs: []Box -> xs -- Error [E0522]: container element mode laundering
    let snap = Box.{ n: 7 }
    let mut left: []Box = [snap]
    let mut right: []Box = [snap]
    Array::push(mut left, snap)
    Array::push(mut right, snap)           -- OK: shared immutable snapshot has no live/mutable origin
    let mut y = Box.{ n: 3 }
    assert(len(ref left) == 2 && take_shared(mut x, new [^mut y]) == 6 && y.n == 6)
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
                         "{" { Newline } [ EffectMemberList ] "}"
EffectMemberList     ::= ( EffectSpread | EffectOpDecl ) { ( "," | Newline ) ( EffectSpread | EffectOpDecl ) } [ "," ] { Newline }
EffectSpread         ::= ".." TypeReference
EffectOpDecl         ::= { MetaAttr } "fn" ValueName "(" [ ParameterTypeList ] ")" [ StateAnnot ] "->" ReturnType
EffectAnnot          ::= EffectClause { EffectClause }
EffectClause         ::= "@" ( SystemEffect | EffectIdentifier )
SystemEffect         ::= "io" | "fiber"
EffectIdentifier     ::= { "Super" "::" } { PathSegment "::" } PascalCase [ GenericArgs ]
EffectOperationRef   ::= { "Super" "::" } { PathSegment "::" } PascalCase [ GenericArgs ] "::" ValueName
WithStatement        ::= "with" HandlerSpec
HandlerSpec          ::= HandlerArm
                       | "{" { Newline } [ HandlerArm { ( "," | Newline ) HandlerArm } [ "," ] { Newline } ] "}"
HandlerArm           ::= EffectOperationRef "(" [ HandlerParameterList ] ")" "->" Expression
HandlerParameterList ::= HandlerParameter { "," HandlerParameter } [ "," ]
HandlerParameter     ::= [ "mut" | "^mut" | "ref" | "new" ] UnmodifiedPattern
```

| Handler rule | Requirement |
| :--- | :--- |
| Scope & loans of `with` | `with` installs its handler arms over the remainder of the enclosing block (operations inside an arm dispatch to outer handlers). Captured `mut`/`^mut`/`var`/`ref` bindings carry an active handler loan: freezing/moving `new x` (`E0535`/`E0548`) while `with` holds `x`, or overlapping `x` across a call/`for`/projection that may exercise the handled `@Eff`, fails `E0523`/`E0524`/`E0526`/`E0537` |
| Effect spreading (`..SubEff`) | `..SubEff` splices an accessible `eff`'s operations into `SupEff` (`E0620` on non-effect, `E0313` on spread cycles, `E0622` on conflicting operation signatures); operations remain invoked/handled via `SubEff::op` or `SupEff::op`, and `@SupEff` covers `@SubEff` in `MatchCallable` and `with` discharge |
| Validation (`E0621`, `E0622`, `E0345`, `E0406`) | Arms must target declared `eff` operations (`E0621` on ordinary functions or `@io`/`@fiber`), without duplicate arms per `with` (`E0622`). Parameters must be irrefutable (`E0345`), non-`var` (`E0403`), and match the operation's declared parameter modes (`E0406`). Temporary `mut` operation authority ends when the arm returns |
| Discharge (`E0612`, `E0618`) | Covering all operations in a callee's known footprint (or all operations of an abstract `@Eff` parameter) discharges `@Eff`; uncovered operations remain required on named callers (`E0612`). Block-local `eff` declarations must be discharged before block exit (`E0618`) |
| Lexical closure capture | Closures created inside `with` capture active handlers needed for their residual `eff` operations (`&capture` / `&up` when capturing runtime state; pure stateless `fn` handlers add no state obligation). Scoped `use` resources or `Task` handles cannot escape via handler capture (`E0604`) |

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
        -- Array::len(xs)  -> 0,              -- Error [E0621]: module function is not an 'eff' operation
    }
    -- let frozen: []str = new lines          -- Error [E0535]: active 'with' handler holds write loan on 'lines'
    -- for ref lines as s { Log::info(s) }    -- Error [E0526]: '@Log' handler mutates 'lines' during iteration
    let res = audit_event("login")
    assert(res == "1700:login" && lines == ["1700:login"])
}
test_audit()
-- fn bad_eff() @int -> () {}                 -- Error [E0620]: 'int' is not a declared effect label
-- fn bad_mod_eff() @Fiber -> () {}           -- Error [E0620]: 'Fiber' is a module; write '@fiber'
```

### Built-in System Effects

The prelude predeclares two lowercase operational system effect labels (`@io` and `@fiber`), keeping `PascalCase` module bindings (`use ril/io`, `use ril/fiber`, `use ril/channel`) collision-free. Writing non-effect names after `@` fails `E0620`, and targeting `@io` or `@fiber` in `with ... ->` fails `E0621`.

| System effect | Purpose & discharge boundary |
| :--- | :--- |
| `@io` | External host I/O, timers, filesystem/network access, and stateful `.d.ril` calls; serviced by the host runtime on `fn main` |
| `@fiber` | Cooperative fiber suspension, channel waiting, structured nurseries, and cancellation checkpoints; serviced on `fn main` or discharged deterministically by `Fiber::run` |

### Panic Absorption with absorb_panic

`absorb_panic` contains synchronous defects behind an unwind-safe boundary, running active `use` cleanup handlers inside the protected closure before returning `Err (PanicError::Panicked info)`.

```ril
-- Prelude declarations:
pub opaque type PanicInfo = str
pub type PanicError { Panicked PanicInfo }

pub fn panic_message(info: PanicInfo) -> str
pub fn absorb_panic<T>(via action: fn() @& -> infer T) -> infer !<T, PanicError>
```

```ril
fn parse_header(parts: []str) -> str { parts[1] }

fn isolated_parse(parts: []str) -> !<str, PanicError> {
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
| Unwind safety (`E0608`) | `action` must not observe or mutate external `var`/`mut`/`^mut`/`ref` state, move outer `new` channel endpoints (`Sender`/`Receiver`), access `.d.ril` `opaque` handles, emit unhandled operational effects (including `@io` / `@fiber`) or stateful outer `with` handlers, or leak mutable/`use` captures (`E0608`). Confined local `var` / `let mut` / `use` state and pure stateless outer or local `with` handlers are allowed |
| Sealed `PanicInfo` (`E0301`, `E0308`) | `PanicInfo` is an opaque prelude type (`E0301` on direct construction, `E0308` on representation penetration); `panic_message(info)` extracts the diagnostic message at run time (`E0810` in static evaluation) |
| Double-Fault termination | If a `use` cleanup handler panics while unwinding an earlier panic, the runtime terminates the OS process immediately without returning `Err` |

### Structured Fiber Concurrency and Channels

`ril/fiber` provides structured cooperative nurseries using lexical-region-bound `Scope` and `Task<T>` handles (carrying an internal static region $\sigma$ checked identically to `Draft<T>` confinement), alongside typed multi-producer single-consumer channels in `ril/channel`.

```ril
-- Canonical declarations in ril/fiber:
pub opaque type Scope
pub opaque type Task<T |> Sendable>
pub type Zip<A, B> = .{ via first: A, via second: B }
pub type TaskFault { ..PanicError, Cancelled }
pub type TimeoutError { Elapsed }

pub fn run<T |> Sendable>(via action: fn() @& -> infer T) -> infer T
pub fn yield_now() @fiber -> ()
pub fn sleep_ms(ms: int) @io @fiber -> ()
pub fn is_cancelled() -> bool
pub fn uncancellable<T>(via action: fn() @& -> infer T) -> infer T
pub fn timeout_ms<T |> Sendable>(ms: int, via work: fn() @& -> infer T) @io @fiber -> infer !<T, TimeoutError>

pub fn scope<T>(via body: fn(mut Scope) @& -> infer T) @fiber -> infer T
pub fn try_scope<T |> Sendable, E |> Sendable>(
    via body: fn(mut Scope) @& -> infer !<T, E>,
) @fiber -> infer !<T, E>
pub fn supervise<T |> Sendable>(via work: fn() @& -> infer T) @fiber -> infer !<T, TaskFault>

pub fn spawn<T |> Sendable>(mut s: Scope, via work: fn() @& -> infer T) &mut -> new Task<T>
pub fn join<T |> Sendable>(mut s: Scope, via task: Task<T>) @fiber &mut -> infer T
pub fn cancel<T |> Sendable>(mut s: Scope, new task: Task<T>) @fiber &mut -> ?T
pub fn cancel_scope(mut s: Scope) &mut -> ()

pub fn zip<A |> Sendable, B |> Sendable>(
    via left: fn() @& -> infer A,
    via right: fn() @& -> infer B,
) @fiber -> infer Zip<A, B>
pub fn try_zip<A |> Sendable, B |> Sendable, E |> Sendable>(
    via left: fn() @& -> infer !<A, E>,
    via right: fn() @& -> infer !<B, E>,
) @fiber -> infer !<(A, B), E>
pub fn map<T |> Sendable, U |> Sendable>(xs: []T, via work: fn(T) @ -> infer U) @fiber -> infer []U
pub fn try_map<T |> Sendable, U |> Sendable, E |> Sendable>(
    xs: []T,
    via work: fn(T) @ -> infer !<U, E>,
) @fiber -> infer !<[]U, E>
pub fn race<T |> Sendable>(via left: fn() @& -> infer T, via right: fn() @& -> infer T) @fiber -> infer T
```

```ril
-- Canonical declarations in ril/channel:
pub opaque type Sender<T |> Sendable> use close
pub opaque type Receiver<T |> Sendable>
pub type ChannelPair<T |> Sendable> = .{ mut tx: Sender<T>, mut rx: Receiver<T> }
pub type SendError<T> { Closed T }
pub type TrySendError<T> { Full T, Closed T }
pub type TryRecvError { Empty, Closed }

pub fn bounded<T |> Sendable>(capacity: int) -> new ChannelPair<T>
pub fn unbounded<T |> Sendable>() -> new ChannelPair<T>
pub fn clone<T |> Sendable>(ref tx: Sender<T>) -> new Sender<T>
pub fn send<T |> Sendable>(mut tx: Sender<T>, via item: T) @fiber &mut -> infer !<(), SendError<T>>
pub fn try_send<T |> Sendable>(mut tx: Sender<T>, via item: T) &mut -> infer !<(), TrySendError<T>>
pub fn recv<T |> Sendable>(mut rx: Receiver<T>) @fiber &mut -> new ?T
pub fn try_recv<T |> Sendable>(mut rx: Receiver<T>) &mut -> new !<T, TryRecvError>
pub fn close<T |> Sendable>(new tx: Sender<T>) -> ()
pub fn close_recv<T |> Sendable>(new rx: Receiver<T>) -> ()
pub fn drain<T |> Sendable>(new rx: Receiver<T>, via f: fn(via T) @& -> ()) -> ()
```

```ril
use ril/fiber
use ril/channel

fn sum_pipeline(limit: int) @fiber -> int {
    Fiber::scope \mut s -> {
        let Channel::ChannelPair.{ mut tx, mut rx } = Channel::bounded(16)
        let producer = Fiber::spawn(mut s) \-> {
            use mut sender = new tx
            for 1..=limit as i {
                match Channel::send(mut sender, i * i) {
                    Ok ()   -> (),
                    Err _   -> break,
                }
            }
        }
        -- let snap_xs = [1, 2]
        -- let _ = Channel::send(mut tx, snap_xs)              -- Error [E0548]: shared snapshot requires 'clone(snap_xs)'
        -- var shared_cnt = 0
        -- let _ = Fiber::spawn(mut s) \-> { shared_cnt += 1 } -- Error [E0601]: cannot capture outer 'var' across fiber
        -- var trace_n = 0
        -- with Trace::mark() -> { trace_n += 1 }
        -- let _ = Fiber::spawn(mut s) \-> Trace::mark()       -- Error [E0615]: stateful handler cannot cross fiber boundary
        var total = 0
        while let Some v = Channel::recv(mut rx) {
            total += v
        }
        Fiber::join(mut s, new producer)
        total
    }
where
    -- eff Trace { fn mark() -> () }
}
assert(Fiber::run(\-> sum_pipeline(4)) == 30)
```

| Concurrency & channel rule | Requirement |
| :--- | :--- |
| `Sendable` (`E0301`) | Admits value types, `.ril` shared objects without `ref`/`^mut` members whose constituents are `Sendable`, `Sender<U>` / `Receiver<U>`, and pure/stateless callables limited to `@io`, `@fiber`, and pure `fn` effects; rejects `Scope`, `Task`, `Draft`, `use` bindings, and `.d.ril` `opaque` handles |
| Cross-fiber isolation (`E0601`, `E0615`, `E0549`) | Every fiber capture must satisfy `Sendable` (`E0601` / `E0301`) and cannot capture `ref`, `mut`, `^mut`, `var`, `use` bindings (`E0601`), or stateful outer `fn` handlers (`E0615`). Direct single-shot closures (`run`, `spawn`, `zip`, `try_zip`, `race`, `supervise`, `timeout_ms`) may consume qualified `Sendable` outer `new` bindings once (`E0549` on reuse; contained sources must independently satisfy isolation) |
| Lexical region $\sigma$ (`E0604`) | Each `scope` / `try_scope` creates a fresh static region $\sigma$ shared by its `Scope` parameter and spawned `Task<T>` handles. Neither `Scope` nor `Task<T>` may escape `body` or cross into another nursery's `join`/`cancel` (`E0604`). Normal `scope` exit awaits unjoined tasks in reverse spawn order; `try_scope` `Err` cancels and drains siblings |
| `Result` inspection & supervision (`E0720`, `E0608`) | `Task<!<T, E>>` must be `join`ed or `cancel`ed (`E0720`); `Receiver<!<T, E>>` requires `drain` (`close_recv` fails `E0720`); `zip`, `map`, `try_*`, `race`, `timeout_ms`, and `supervise` reject nested `!<U, E2>` payloads (`E0720`). `supervise` enforces `E0608` unwind safety while permitting `@fiber` suspension/cancellation (yielding `TaskFault::Cancelled`) |
| Task & channel payloads (`E0548`, `E0535`) | `Channel::send` / `try_send` accept value copies or complete `new` `SharedObject` graphs free of old-source boundaries (`E0548` on frozen snapshots, `ref`/`mut` borrows, or `new` wrappers over old sources; pass `clone(...)`), so `recv` / `try_recv` return `new ?T` / `new !<T, TryRecvError>`. `join(mut s, new task)` preserves `work`'s `infer T` qualification; plain/`ref` `join` freezes `T` (`E0535`) |

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
meta let _ = assert(<OptInt> == <?int> && <?int> == <Option<int>> && <!<int, str>> == <Result<int, str>>)
meta let _ = assert(<int> != <f64>)
-- let bad_bare = int                  -- Error [E0319]: bare type in value expression; write '<int>'
```

### Pure Type Functions and Result Restrictions

<a id="finite-evaluation-with-div"></a>

```ebnf
MetaLetDecl ::= [ Visibility ] "meta" "let" ( ScreamingSnakeCase | Wildcard ) [ ":" TypeExpression ] "=" Expression
MetaFnDecl  ::= { MetaAttr } [ Visibility ] "meta" "fn" ValueName [ GenericParams ]
                "(" [ ParameterList ] ")" ReturnSpec [ SignatureWhereClause ] Block
```

- **Pure Static Domain (`E0335`, `E0812`, `E0813`, `E0816`)**: `TypeFunctionExpr`, `meta fn`, and `meta let` evaluate in a pure compile-time environment with local `var`/`let mut`, confined closures, loops, and recursion, forbidding `@Eff` / `&State` annotations (`E0335` on type functions, `E0813` on `meta fn`). `meta fn` returns and `meta(...)` attributes cannot expose `Type<T>` tokens (`E0812`); `meta fn` returns, `meta let` constants, and `meta(...)` attributes cannot export callables or `use` resources, and `RunTime` values/parameters/storage/closures cannot materialize `Type<T>` (`E0816`).
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
-- meta fn bad_io() @io -> int { 1 }   -- Error [E0813]: 'meta fn' must be pure
-- fn rt_tok(t: Type<int>) -> () {}    -- Error [E0816]: runtime parameter cannot hold 'Type<int>'
-- type Spin = \T -> Spin<T>
-- type Boom = Spin<int>               -- Error [E0811]: compile-time evaluation budget exceeded
```

### Disjoint Call Families and Branch Pruning

| Evaluation context | Permitted calls (`E0810` otherwise) |
| :--- | :--- |
| `TypeEval` (type functions, guards) | Type functions, `meta fn`, confined closures, static reflection, and dual-phase core operations (`len`, `inner`, `clone`, `derive`, `assert`, `panic`, `String::inspect`, plus pure `Array`, `Map`, `Set`, `String`, `Bytes`, and `Numeric` operations) |
| `MetaValue` (`meta fn`, `meta let`, `meta(...)`) | `meta fn`, confined closures, static reflection, and dual-phase core operations |
| `RunTime` (`fn`, closures) | Ordinary `fn`, closures, foreign `.d.ril` `fn`, built-ins, plus direct saturated `meta fn` calls with static arguments (folded to immutable snapshots) |

In `RunTime` functions, `if` / `match` branches over `meta let` constants (such as `Platform::OS`) are fully type-, mode-, and effect-checked on all branches, then statically unreachable branches and `.d.ril` symbols referenced solely within them are pruned before code generation and linking. Static `match <T>` over a rigid type parameter checks each arm under its static token evidence and selects the matching arm at specialization. Negative static sizes/counts where nonnegative static values are required fail `E0815`.

### Static Introspection

```ebnf
TypeProjection            ::= ( PrimaryType | TupleType | RecordType | TypeProjection ) "." ( FieldLabel | PascalCase | TupleIndex | "(" Expression ")" )
MappedRecordType          ::= ".{" [ ModeModifier ] MappedComprehensionClause ":" TypeExpression "}"
MappedComprehensionClause ::= "[" ForIterable "as" Pattern "]"
ModeModifier              ::= RecordFieldMode | ValueName
```

- **Constituent Projection (`T.(k)`)**: Projects field type `T.field` / `T.("field")` on accessible records (structural, `nominal`, and in-scope `opaque`), component type `T.0` / `T.(0)` on tuples, and payload type `T.Variant` / `T.("Variant")` on transparent sums (`()` for unit variants; `E0308` on sealed `.ril` `opaque` types, `E0907` on `.d.ril` types).
- **Product Coordinates & Sum Variants (`coords`, `variants`, `MemberMode`)**:
  - Prelude `MemberMode` provides value constructors `MemberMode::Let`, `Var`, `Mut`, `SharedMut`, `Ref`, `VarMut`, `VarSharedMut`, and `VarRef` (corresponding to type-level `MemberModeLiteral` spellings `let`, `var`, `mut`, `^mut`, `ref`, `var mut`, `var ^mut`, `var ref`).
  - `coords(<T>) -> [](MemberMode, CoordKey<T>)` enumerates `(mode, field_name)` pairs in UTF-8 byte order for accessible records (`CoordKey<T>` = `str`) and `(MemberMode::Let, index)` pairs in ascending index order for tuples (`CoordKey<T>` = `int`; `()` yields `[]`) (`E0358` on non-products; `E0308` when sealed).
  - `variants(<T>) -> []str` enumerates deduplicated variant names in UTF-8 byte order for closed transparent sums (`E0301` on non-sums; `E0308` when sealed or open `..`).
- **Mapped Record Types (`.{ [m] [expr as pat]: Type }`)**: Comprehension keys must have type `str` (`E0341`), satisfy `FieldLabel` syntax and non-keyword rules (`E0815` otherwise), and contain no duplicates (`E0210`); value-type fields with `mut`/`^mut`/`ref` modes fail `E0402`, and invalid mode sorts fail `E0356` / `E0357`.
- **Metadata Introspection (`Reflect`)**:
  - `Reflect::attrs<T, A>(target: Type<T>) -> []A`
  - `Reflect::field_attrs<T, A>(target: Type<T>, meta key: str |> Key<T>) -> []A`
  - `Reflect::variant_attrs<T, A>(target: Type<T>, meta variant: str) -> []A`
  - `Reflect::has_default<T>(target: Type<T>, meta key: str |> Key<T>) -> bool` (`true` iff `T` is a `nominal` or in-scope `opaque` record whose root field `key` declares `= expr`)

```ril
type Select = \T: .{ ..R }, keys: []str -> {
    let chosen = coords(<T>) |> Array::filter(\(_, k) -> Array::contains(keys, k))
    <.{ m [chosen as (m, k)]: T.(k) }>
}

type Model = .{ id: int, var title: str, mut rows: []int }
type Patch = Select<Model, ["title", "rows"]> -- .{ var title: str, mut rows: []int }
nominal type Args = .{ query: str, limit: int = 10 }
meta let _ = assert(Reflect::has_default(<Args>, "limit") && !Reflect::has_default(<Args>, "query"))
meta let _ = assert(len(coords(<Args>)) == 2 && coords(<(int, str)>)[0] == (MemberMode::Let, 0))
-- meta let _ = coords(<int>)            -- Error [E0358]: 'coords' requires a transparent record or tuple type
-- type BadMap = .{ [[1, 2] as k]: int } -- Error [E0341]: mapped record key must have type 'str'
-- type BadKey = .{ [["fn"] as k]: int } -- Error [E0815]: keyword 'fn' is not a valid FieldLabel
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
                        | "?" TypePatternInner
                        | TypeResultPattern
                        | TypeTuplePattern
                        | TypeRecordPattern
                        | TypeArrayPattern
                        | TypeMapPattern
                        | RigidNominalPattern
                        | PrimitivePattern
                        | LiteralPattern
TypeResultPattern     ::= "!<" TypePatternInner "," TypePatternInner [ "," ] ">"
TypeTuplePattern      ::= "(" ")"
                        | "(" TypePatternInner "," TypePatternInner { "," TypePatternInner } [ "," ] ")"
TypeRecordPattern     ::= ".{" [ TypeRecordPatternList ] "}"
TypeRecordPatternList ::= TypeRestPattern [ "," ]
                        | TypePatternField { "," TypePatternField } [ "," TypeRestPattern ] [ "," ]
TypePatternField      ::= [ MemberMode ] FieldLabel ":" ( TypePatternInner | "_" )
                        | "let" PascalCase FieldLabel ":" ( TypePatternInner | "_" )
TypeRestPattern       ::= ".." [ "let" PascalCase ]
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
    <!<let OkT, _>> -> <OkT>,
    <?let Inner>    -> <Inner>,
    _               -> <T>,
}
meta let _ = assert(<UnwrapResult<!<int, str>>> == <int>)
meta let _ = assert(<UnwrapResult<Result<int, str>>> == <int>)
meta let _ = assert(<UnwrapResult<?str>> == <str>)
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
             | LetDecl | TypeDecl | NominalTypeDecl | OpaqueTypeDecl
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
| **Top-Level Purity (`E0202`, `E0906`, `E0205`)** | File and `sub` top-level allow only pure deeply immutable `ScreamingSnakeCase` constants (`let` and `meta let`, requiring zero `&up` annotations when read). Mutable, shared, live `ref`, or `use` resource top-level bindings (`var`, `let mut`, `let ^mut`, `let ref`, `use [mut] x = ...`) are prohibited (`E0906`); impure initializers fail `E0202`; top-level `?` fails `E0205` |

```ril
-- File: math/circle.ril
pub let PI = 3.141592653589793
pub(pkg) let INTERNAL_EPS = 1.0e-9
type Hidden = .{ r: f64 }

pub fn area(r: f64) -> f64 { PI * r * r }       -- Zero '&up' needed for pure module constant 'PI'
pub(pkg) fn label_pkg(pkg: str) -> str { pkg }  -- 'pkg' is contextual in pub(pkg) and free as an identifier

pub sub UnitCircle {
    pub opaque type Rad = f64
    pub fn zero() -> Rad { 0.0 }                    -- Bidirectional Rad <-> f64 inside 'UnitCircle'
    pub fn circumference() -> f64 { 2.0 * Super::PI } -- Hermetic 'sub' reaches parent 'PI' via 'Super::'
    -- let _ = PI                               -- Error [E0204]: 'PI' not in scope without 'Super::'
}
-- let _r: UnitCircle::Rad = 1.0                -- Error [E0301]: expected 'UnitCircle::Rad', found 'f64'
-- let _k = coords(<UnitCircle::Rad>)           -- Error [E0308]: 'Rad' representation is sealed outside 'UnitCircle'
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
- **Visibility Lattice & Interface Consistency (`E0201`, `E0910`)**: `private(scope) < pub(pkg) < pub`; reachability along an inline `sub` path is capped by every enclosing `sub`, and `pub use` cannot widen target visibility (`E0201`). Every type, non-opaque field/variant, `TypeFunctionExpr` body, parameter/field default, `use` cleanup function, and unhandled `@Eff` in a declaration must be accessible from every scope that can reach that declaration (`E0910`; `pub opaque` internal representations remain private).

```ril
use pkg/math/circle as Circle
use pkg/math/circle::UnitCircle
sub Helper {
    type Local = .{ x: int }
    -- pub fn expose() -> Local { Local.{ x: 1 } } -- Error [E0910]: reachable in file, where 'Local' is private
}
-- use pkg/math/missing                -- Error [E0208]: module 'pkg/math/missing' not found
-- use pkg/math/circle::nonexistent    -- Error [E0209]: 'nonexistent' not found in 'Circle'
-- let _ = Circle::Hidden.{ r: 1.0 }   -- Error [E0201]: 'Hidden' is private to 'Circle'
-- use pkg/net/a_b                     -- Error [E0102]: derived 'AB' violates PascalCase acronym rule
```

### Program Entry Point

```ril
use ril/file

fn main() @io @fiber -> !<(), str> {
    let raw = File::read("config.json")?
    if raw == "" { Err "empty config" } else { Ok () }
}
-- Missing 'fn main' in executable root       -- Error [E0903]
-- fn main(argc: int) -> int { argc }         -- Error [E0904]: invalid 'main' signature
-- sub Sub { fn main() -> () {} }             -- Error [E0904]: 'main' prohibited inside 'sub'
-- pub let ROOT_EXPORT = 1                    -- Error [E0905]: 'pub' prohibited in executable root
```

`main` must be a non-public, non-generic ordinary `fn` at the executable root taking `()` and returning `()` or `!<(), str>` (`E0903` if missing, `E0904` if malformed or inside `sub`). It may declare `@io` and `@fiber` (`E0612` on unhandled user-defined `eff`). Returning `()` / `Ok ()` exits `0`; returning `Err msg` prints `msg` + `\n` to stderr and exits `1`.

### Prelude Scope

The ambient prelude encloses every compilation unit and inline `sub`, predeclaring primitive types, `Option<T>` (`?T`; `Some T`, `None`), `Result<T, E>` (`!<T, E>`; `Ok T`, `Err E`), `Set<T>`, `PanicInfo`, `PanicError`, `MemberMode`, `Draft<T>`, `@io`, `@fiber`, static guards/operations `SharedObject`, `Sendable`, `LenTarget`, `Tuple`, `NominalWrapper`, `Unwrap`, `CoordKey`, `Key`, and core modules `Array`, `Map`, `Set`, `String`, `Bytes`, `Numeric`, `Reflect`. Explicit imports (`use ril/io`, `use ril/file`, `use ril/os`, `use ril/fiber`, `use ril/channel`, `use ril/platform`, `use ril/math`, `use ril/crypto`) bring system, concurrency, and platform APIs into scope.

#### Built-in Foundational Operations

| Built-in | Canonical signature | Phase & contract |
| :--- | :--- | :--- |
| `len` | `pub fn len<T \|> LenTarget>(via item: T) -> int` | Dual-phase: scalar count of `str`, byte count of `bytes`, element/entry count of `[]T`, `[K: V]`, `Set<T>` (admits `ref` on collections at run time; `E0401` on `ref str`) |
| `inner` | `pub fn inner<W \|> NominalWrapper>(via wrapper: W) -> infer Unwrap<W>` | Dual-phase: unwraps accessible `.ril` `nominal` wrapper (or `Draft<W>`) to its payload (`()` for unit nominals; preserves `ref`/`mut` access; `E0907` on `.d.ril` nominals, `E0301` on non-nominals) |
| `clone` | `pub fn clone<T \|> SharedObject>(via value: T) -> new T` | Dual-phase: deep copy of clonable `SharedObject` graph into isolated `new T` (`E0301` on value types or graphs containing `.d.ril` `opaque` / concurrency / `Draft` handles; `E0530` on live/mutable closures) |
| `derive` | `pub fn derive<T \|> SharedObject>(base: T, recipe: fn(mut Draft<T>) @& -> ()) -> T` | Dual-phase: path-targeted functional update on immutable `SharedObject` (`E0536`, `E0308`, `E0607`) |
| `absorb_panic` | `pub fn absorb_panic<T>(via action: fn() @& -> infer T) -> infer !<T, PanicError>` | Run-time: unwind-safe panic containment (`E0608`) |
| `panic_message` | `pub fn panic_message(info: PanicInfo) -> str` | Run-time: extracts human-readable message from `PanicInfo` (`E0810` in static eval) |
| `type_name` | `pub meta fn type_name<T>(token: Type<T>) -> str` | Static only: diagnostic display string of `T` |
| `coords` | `pub meta fn coords<T>(token: Type<T>) -> [](MemberMode, CoordKey<T>)` | Static only: `(mode, key)` pairs of accessible record (`str` keys) or tuple (`int` keys) `T` (`E0358` non-product, `E0308` sealed) |
| `variants` | `pub meta fn variants<T>(token: Type<T>) -> []str` | Static only: variant tags of closed transparent sum `T` (`E0301` non-sum, `E0308` sealed/open) |
| `panic` | `pub fn panic(message: str) -> never` | Dual-phase: LIFO panic unwinding at run time; `E0831` in static eval |
| `assert` | `pub fn assert(condition: bool, message: str = "assertion failed") -> ()` | Dual-phase: panics with `message` when `false` at run time; `E0830` when `false` in static eval |
| `print` / `println` | `pub fn print(text: str) @io -> ()`<br>`pub fn println(text: str) @io -> ()` | Run-time (`@io`): writes UTF-8 text (plus `\n` for `println`) to stdout |

### Mandatory Inspection of Fallible Results

Every `!<T, E>` (`Result<T, E>`)—including `!<T, E>` parameters—must be inspected before normal scope exit (`E0720`): matched (`match`, `if let`, `let ... else`), compared in a reached `==` / `!=` directly against `Ok <expr>` or `Err <expr>`, propagated (`?`), handled (`??`), passed to an explicitly `!<T, E>`-typed parameter, or returned. Discarding a `Result`, binding to `_`, instantiating an unconstrained generic parameter with `!<T, E>`, wrapping in uninspected composite values, comparing two non-constructor `Result` variables, or overwriting its last binding fails `E0720`.

```ril
fn write_entry(line: str) @io -> !<(), str> {
    println(line)
    Ok ()
}
fn drop_any<T>(_x: T) -> () {}

fn handle_log() @io -> !<(), str> {
    -- write_entry("dropped")             -- Error [E0720]: unused fallible Result
    -- let _ = write_entry("ignored")     -- Error [E0720]: '_' does not inspect Result
    -- drop_any(write_entry("generic"))   -- Error [E0720]: unconstrained generic parameter does not inspect Result
    -- let _ = Some (write_entry("wrap")) -- Error [E0720]: wrapped Result discarded uninspected
    -- let a = write_entry("x")
    -- let b = write_entry("y")
    -- let _ = (a == b)                   -- Error [E0720]: non-constructor comparison does not inspect Result
    write_entry("propagated")?            -- OK: propagated via '?'
    write_entry("fallback") ?? \_e -> ()  -- OK: handled via '??'
    let r = write_entry("tested")
    assert(r == Ok ())                    -- OK: reached comparison against 'Ok ()' inspects Result
    let Ok () = write_entry("guarded") else { return Err "failed" }
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
| **`E0357`** | [`IncompatibleMemberModeError`](#record-types-and-row-polymorphism); [Member Modes and Implicit Schema Parameters](#member-modes-and-implicit-schema-parameters) |
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
| **`E0601`** | [`CrossTaskAuthorityError`](#structured-fiber-concurrency-and-channels) |
| **`E0604`** | [`ScopedOrRegionEscapeError`](#scoped-resource-bindings); [Structured Fiber Concurrency and Channels](#structured-fiber-concurrency-and-channels) |
| **`E0607`** | [`DeriveDraftEscapeError`](#functional-updates-via-derive) |
| **`E0608`** | [`UnwindUnsafePanicBoundaryError`](#panic-absorption-with-absorb_panic) |
| **`E0612`** | [`UnhandledEffectError`](#effect-declarations-and-handlers) |
| **`E0613`** | [`ValueEffectAnnotationError`](#type-definition-boundaries) |
| **`E0615`** | [`ConcurrentEffectBoundaryError`](#structured-fiber-concurrency-and-channels) |
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
