# The Ril Language Specification

**Version:** 0.2.0  
**Status:** Canonical Reference Specification  
**Format:** Code-First Normative Document  

---

## Document Conventions

This document defines Ril syntax, static semantics, access modes, state and provenance tracking, scoped effects, abstract-machine execution, and diagnostic error codes.

- **Normative Force**: Grammar productions, rule tables, judgment premises, and inline code annotations (`-- OK`, `-- Error [EXXXX]`, `-- Panics`) are normative. **Must** and **must not** express requirements and prohibitions; **may** permits an alternative; **should** gives advisory guidance.
- **Snippets vs. Complete Source Files**: Code blocks are independent normative snippets unless marked as complete source files.
  - Abbreviated named callables in independent snippets denote their compiler-completed signatures under [mandatory signature completion](#mandatory-signature-inference-and-completion), unless testing missing annotations (`E0510`, `E0544`, `E0612`).
  - Complete source files spell all required effect and state/provenance annotations.

| Distinction | Ril meaning |
| :--- | :--- |
| Binding / access | `let`, `var`, and `use` govern slot scope and replacement; plain (unmodified), `ref`, `mut`, `^mut`, and `new` govern path access and authority |
| Provenance / `new` subgraphs | Provenance tracks which existing sources a value references and which parts are `new`; `new` lets the target choose modes for newly constructed subgraphs while nested existing sources keep their authority and aliases |
| Values / shared objects | `bool`, `int`, `f64`, `str`, `bytes`, and `()` copy by value; records, nonempty tuples, collections, and sums have automatically reclaimed object identity |
| Record forms / constructors | Named and anonymous records attach `.{...}` (`User.{ id: 1 }`); payload variants and non-record nominal constructors use tight `(...)` (`Ok(42)`, `Ok()`, `Rect(10.0, 20.0)`, `UserId(42)`) |
| Aliases / nominal / opaque | `type A = B` is a structural alias; `nominal type A = B` has distinct public identity; `opaque type A = B` seals representation outside its defining file or `sub` |
| Reachable authority use | `var` requires reachable slot replacement, `mut` requires writable or `new`-handoff use, `^mut` parameters require surviving retention, and named state annotations must be minimal (`E0527`, `E0529`) |
| `where` / checks & guards | Dual-tier `where` hoists helper declarations (`type`, `fn`, `meta fn`, block `eff`); `\|>` runs static checks on generic parameters and fallible signature guards on runtime parameters/returns |
| Purity / defects | Purity excludes outward effects and non-pure state/provenance obligations; finite defects initiate LIFO panic unwinding |

### Ril at a Glance

```ril
type Cell = .{ var count: int }
eff Clock { fn now_ms() -> int }

-- Access modes flow through generic calls ('via' / 'infer') and '&return(...)'.
fn relay<T>(via x: T) -> infer T { let via y = x; y }
fn bump(mut c: Cell) &mut -> () { c.count += 1 }
fn share_in_list(^mut c: Cell) &^mut &return(^mut c) -> new [^mut]Cell { [^mut c] }
fn stamp(ref c: Cell) @Clock -> str { "{Clock::now_ms()}:{c.count}" }

fn demo() -> str {
    let mut cell = Cell.{ count: 1 }           -- Unshared writable 'new'-qualified local
    bump(mut cell)                             -- Call-scoped write; explicit 'mut' marker
    let mut shared = share_in_list(^mut cell)  -- Unshared 'new' list holding shared '^mut' cell
    shared[0].count += 1                       -- Updates 'cell.count' to 3

    let snap = clone(ref cell)                 -- Isolated deeply immutable snapshot
    let mut staged = Cell.{ count: snap.count }
    let mut next = relay(new staged)           -- Single-use 'new' handoff ends 'staged'
    bump(mut next)                             -- Updates 'next.count' to 4
    assert(snap.count == 3 && next.count == 4)

    with Clock::now_ms = \-> 1700              -- Lexically scoped effect handler
    stamp(ref next)                            -- "1700:4"
}
```

| Mode | Meaning | Write? | Aliases? |
| :---: | :--- | :---: | :--- |
| *(plain)* | Deeply immutable snapshot or value copy | No | Freely aliased; zero live writers |
| `ref` | Live read-only view | No | Observes a live or immutable object |
| `mut` | Unshared writable (or call-scoped write) | Yes | No overlapping writes or reads during call |
| `^mut` | Shared writable | Yes | Explicitly acknowledged surviving shared writers |
| `new` | Newly constructed subgraph | Target chooses | No outside aliases into `new` subgraph; ends source on `new x` |

---

## Table of Contents

- [The Ril Language Specification](#the-ril-language-specification)
  - [Document Conventions](#document-conventions)
    - [Ril at a Glance](#ril-at-a-glance)
  - [Notation, Abstract Machine, and Conformance](#notation-abstract-machine-and-conformance)
    - [Grammar Notation](#grammar-notation)
    - [Program Conformance](#program-conformance)
    - [Diagnostic Classification](#diagnostic-classification)
    - [Abstract Machine and Memory Semantics](#abstract-machine-and-memory-semantics)
    - [Failure Model and Purity](#failure-model-and-purity)
    - [Runtime Failure Conditions](#runtime-failure-conditions)
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
    - [Record Types and Open Record Tails](#record-types-and-open-record-tails)
    - [Array, Map, Set, and Tuple Types](#array-map-set-and-tuple-types)
    - [Sum Types and Variant Spreading](#sum-types-and-variant-spreading)
    - [Nominal, Type Alias, and Opaque Types](#nominal-type-alias-and-opaque-types)
    - [Deep Immutability](#deep-immutability)
    - [Type Identity and Subtyping](#type-identity-and-subtyping)
    - [Complete Provenance and Required Annotations](#complete-provenance-and-required-annotations)
    - [Access Mode Inference with via and infer](#access-mode-inference-with-via-and-infer)
    - [Functional Updates via Derive](#functional-updates-via-derive)
    - [Generic Parameters, Defaults, and Static Kinds](#generic-parameters-defaults-and-static-kinds)
    - [Type Definition Boundaries](#type-definition-boundaries)
  - [Static Semantics and Type Kernel](#static-semantics-and-type-kernel)
    - [Static Contexts and Judgment Forms](#static-contexts-and-judgment-forms)
    - [Type Formation and Binding](#type-formation-and-binding)
    - [Type Equivalence and Recursive Types](#type-equivalence-and-recursive-types)
    - [Subtyping, Reception, and Callable Compatibility](#subtyping-reception-and-callable-compatibility)
    - [Bidirectional Expression Checking](#bidirectional-expression-checking)
    - [Structural Joins and Normal Completion](#structural-joins-and-normal-completion)
    - [Generic Type Facts and Definition Checking](#generic-type-facts-and-definition-checking)
    - [Authority, Calls, and Provenance Operations](#authority-calls-and-provenance-operations)
    - [Recursive Summaries and Non-Circular Inference](#recursive-summaries-and-non-circular-inference)
    - [Phase Checking and Static Evaluation](#phase-checking-and-static-evaluation)
    - [Semantic Interfaces and Diagnostic Boundaries](#semantic-interfaces-and-diagnostic-boundaries)
  - [Declarations and Bindings](#declarations-and-bindings)
    - [Binding Modes and Storage Matrix](#binding-modes-and-storage-matrix)
    - [New-Qualified Locals and Mode-Preserving Reception](#new-qualified-locals-and-mode-preserving-reception)
    - [Immutable, Mutable, Shared, and Read-Only View Bindings](#immutable-mutable-shared-and-read-only-view-bindings)
    - [Scoped Resource Bindings](#scoped-resource-bindings)
    - [Declaration Metadata Attributes](#declaration-metadata-attributes)
    - [Foreign Interface Declarations](#foreign-interface-declarations)
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
    - [Let-Else Bindings](#let-else-bindings)
    - [Pattern Matching](#pattern-matching)
    - [Flow-Sensitive Type Narrowing](#flow-sensitive-type-narrowing)
  - [Functions, Closures, and Callables](#functions-closures-and-callables)
    - [Named Function Declarations and Contrast Matrix](#named-function-declarations-and-contrast-matrix)
    - [Callable Types and Signatures](#callable-types-and-signatures)
    - [Return Construction, Access Modes, and Sources](#return-construction-access-modes-and-sources)
    - [Parameter Modes, Caller Obligations, and Defaults](#parameter-modes-caller-obligations-and-defaults)
    - [Anonymous Functions, Trailing Closures, and Projection Accessors](#anonymous-functions-trailing-closures-and-projection-accessors)
    - [Closures and Lexical Environments](#closures-and-lexical-environments)
  - [State and Provenance Tracking](#state-and-provenance-tracking)
    - [Local State Containment, Parameter Mutation, and Sharing](#local-state-containment-parameter-mutation-and-sharing)
    - [State Groups and Captured Layers](#state-groups-and-captured-layers)
    - [Exclusivity and Authority-Escalation Matrix](#exclusivity-and-authority-escalation-matrix)
  - [Scoped Effects, Panic Containment, and Concurrency](#scoped-effects-panic-containment-and-concurrency)
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
    - [Mandatory Inspection of Fallible Results](#mandatory-inspection-of-fallible-results)
  - [Diagnostic Error Codes Summary](#diagnostic-error-codes-summary)
    - [Source Text, Identifiers, and Syntax](#source-text-identifiers-and-syntax)
    - [Names, Initialization, and Field Identity](#names-initialization-and-field-identity)
    - [Types, Expressions, Generics, and Patterns](#types-expressions-generics-and-patterns)
    - [Parameters, Argument Modes, and Defaults](#parameters-argument-modes-and-defaults)
    - [Bindings, State, Access Modes, and Scoped Resources](#bindings-state-access-modes-and-scoped-resources)
    - [Effects, Concurrency, and Escape](#effects-concurrency-and-escape)
    - [Declaration Contexts, Control Flow, and Fallible Values](#declaration-contexts-control-flow-and-fallible-values)
    - [Static Computation](#static-computation)
    - [Module Forms, Entry Points, and Foreign Interfaces](#module-forms-entry-points-and-foreign-interfaces)

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

**Implementation Freedom (As-If Rule)**: This specification defines static validity and observable abstract-machine behavior, not internal compiler or runtime architecture. Conforming implementations may use any execution model (ahead-of-time compilation, JIT compilation, bytecode execution, or interpretation), memory management strategy (tracing GC, cycle-collecting reference counting, escape-analyzed stack or region allocation), generic implementation strategy (monomorphization, specialization, or boxed/witness dispatch), or static-analysis representation, provided every observable result and diagnostic matches this specification.

### Diagnostic Classification

```ril
let valid_unused = 1                   -- OK
-- let bad_type: str = 1               -- Error [E0301]
-- let bad_div = 1 / 0                 -- Error [E0361]: constant zero divisor
meta fn static_ratio(d: int) -> int { 1 / d }
-- meta let Q = static_ratio(0)        -- Error [E0831]: panic during static evaluation
```

Specific diagnostics take precedence over general syntax (`E0120`) or type mismatch (`E0301`) codes (for example, `E0336` for an absent record field and `E0338` for calling a non-callable value). Exact message wording is illustrative; error codes and triggering conditions are normative.

### Abstract Machine and Memory Semantics

Operands and call arguments evaluate strictly left-to-right; short-circuit operators (`&&`, `||`, `??`, `?.`, `?[`) and control transfers (`return`, `break`, `continue`, `?`) skip unevaluated operands.

**Abstract Object-Graph Model**: Throughout this specification, *object graph*, *reachability*, *`new` subgraph*, and *existing-source boundary* are abstract semantic concepts modeling object identity, aliasing, deep immutability, and provenance. They impose no requirement on physical memory layout, heap vs. stack placement, pointer representation, or static-analysis data structures.

```ril
let mut trace: []int = []
let ^mut log = \n: int -> { Array::push(mut trace, n); n }
let total = log(1) + log(2) * log(3)
assert(total == 7 && trace == [1, 2, 3])
```

| Memory property | Requirement |
| :--- | :--- |
| Automatic reclamation | Unreachable shared-object graphs, including reference cycles, must be reclaimed automatically without running user code (no reclamation finalizers) |
| Location-independent identity | Object identity, aliasing, and active `ref`/`mut`/`^mut` relationships are independent of physical storage location; implementations may relocate objects, stack-allocate non-escaping objects, or share immutable representations transparently |
| Authority independence | Object liveness grants no write authority; deterministic `use` cleanup is independent of automatic reclamation |

### Failure Model and Purity

Ril separates expected domain failures from programming defects:

1. **Recoverable Errors (`!<T, E>` / `Result<T, E>` and `?T` / `Option<T>`)**: Carried as explicit values. Every `Result` must be inspected, propagated via `?`, or handled via `??` (`E0720`).
2. **Defects (`panic` / `assert`)**: Trigger deterministic LIFO unwinding of active scopes, running active `use` cleanup functions without requiring signature annotations. Panic-isolation boundaries (`absorb_panic`, `Fiber::supervise`) convert panics into `!<T, PanicError>` / `!<T, TaskFault>`.
3. **Purity**: A callable is pure when its normalized outward effect set is empty and its outward state obligations reduce to empty after local containment. Relations to deeply immutable return sources add no state effect but remain part of return-provenance matching. `never` denotes computations that never complete normally.

```ril
fn parse_port(s: str) -> new !<int, str> {
    if s == "" { Err("empty port") } else { Ok(8080) }
}

fn connect_port(raw: str) -> new !<int, str> {
    let port = parse_port(raw)?        -- OK: propagates Err
    Ok(port)
}
-- parse_port("80")                    -- Error [E0720]: unused Result
```

### Runtime Failure Conditions

| Condition | Outcome |
| :--- | :--- |
| Integer `/ 0` or `% 0` (non-constant divisor) | LIFO panic unwinding (`"division by zero"`) |
| Bit shift `x << k` or `x >> k` with `k < 0` (non-constant `k`) | LIFO panic unwinding (`"negative shift count"`) |
| Out-of-bounds array/byte index `xs[i]` or slice `xs[a..b]` | LIFO panic unwinding |
| `panic(msg)` or false `assert(cond)` | LIFO panic unwinding |
| Secondary panic inside `use` cleanup during active panic/cancel unwinding | Immediate uncatchable program termination (abort; bypasses `absorb_panic`) |
| Unrecoverable execution-resource exhaustion (host memory or call depth) | Immediate uncatchable program termination (abort) |

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

Spaces (` `) and tabs (`\t`) separate tokens. Bare `{ ... }` blocks (`Block`, `sub`, `with`, `eff`, `match`, `type Sum`) and `where` clauses separate items with `;` or `Newline`; `( ... )`, `[ ... ]`, `.{ ... }`, and `< ... >` separate items with `,` and ignore newlines.

```ril
-- Tightly attached delimiters vs. spaced operators:
type User = .{ id: int }
fn f<T>(value: T) -> T { value }
let xs = [1, 2]
let a = 0; let b = 2; let c = 1
let user = User.{ id: 1 }              -- Tight '.{' attaches to 'User'
let pair = f<int>(xs[0])               -- Tight '<', '(', and '['
let cmp  = a < b && b > c              -- Spaced '<' / '>' are relational comparisons
meta let SAME = <!<int, str>>==<!<int, str>> -- Each committed '>' closes one '<'

-- Multi-line continuation on pipeline and field access:
type ParsedUser = .{ name: str }
fn parse_user(raw: str) -> new !<ParsedUser, str> { Ok(ParsedUser.{ name: raw }) }
fn read_label(raw: str) -> new !<str, str> {
    let label = raw
        |> parse_user?
        .name
    Ok(label)
}
```

- **Line continuation**: A newline does **not** emit `Separator` when:
  - the previous token is an operator (`+`, `-`, `*`, `/`, `%`, `&`, `|`, `^`, `<<`, `>>`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `&&`, `||`, `|>`, `as`, `??`, `=`, `+=`, `-=`, `*=`, `/=`, `%=`, `&=`, `|=`, `^=`, `<<=`, `>>=`, `->`, `:`, `,`, `.`, `?.`, `::`);
  - inside unclosed `( ... )`, `[ ... ]`, `.{ ... }`, or committed `< ... >` / `!< ... >`;
  - the next line starts with `.field` (not `.{`), `?.field`, `|>`, `as`, `??`, `else`, `@`, `&`, `->`, or signature `where` (`use` and `with` never continue a preceding line; inside `{ ... }`, `where` opens `BlockWhereClause`).
- **Tight lexical attachment** (no intervening whitespace or newline):
  - Calls/constructors `f(x)`, `Ok(42)`, `Circle(f64)`; indexing `xs[i]`, `xs?[i]`; string slice patterns `str[...]`; named records `User.{ id: 1 }`; result types `!<T, E>`.
  - Raw string/byte prefixes `#"`, `bytes"`, `bytes#"`; cleanup header `use(close)`.
  - Effect/state annotations `@io`, `@Clock`, `&mut`, `&up`, `&up(`, `&return(` (`@&` only when `&` is not followed by a state keyword).
- **Committed `< ... >`**:
  - `<` commits as a delimiter in type/pattern/effect positions, at the start of an expression operand (`<TypeExpression>`), and when tightly attached after an identifier (`f<T>(x)`, `State<int>::get()`) with a matching `>` at the same delimiter depth.
  - Spaced `a < b` lexes as relational `<`. Closing a committed `< ... >` or `!< ... >` consumes one `>` character.

### Syntactic Diagnostic Conditions

| Code | Triggering condition |
| :---: | :--- |
| `E0120` | Unexpected token in the current syntactic production |
| `E0121` | Unexpected `EOF` while a construct remains incomplete |
| `E0122` | Unclosed `(`, `[`, `{`, `.{`, or committed `<` / `!<` delimiter |
| `E0123` | Mismatched closing delimiter (`)`, `]`, `}`) |
| `E0124` | Omitted mandatory delimiter or separator token (`->`, `=`, `:`) |

```ril
type Res { Ok(int); Ready }
let a = Ok(42)                         -- OK
let b = Ready                          -- OK
-- let bad_tok = @                     -- Error [E0120]: unexpected token
-- let bad_eof = 1 +                   -- Error [E0121]: unexpected EOF
-- let bad_open = (1 + 2               -- Error [E0122]: unclosed '('
-- let bad_mismatch = [1, 2)           -- Error [E0123]: mismatched delimiter ')'
-- fn bad_sep(x int) -> int { x }      -- Error [E0124]: missing ':'
```

### Identifiers and Casing Invariants

Ril assigns distinct syntactic roles by ASCII casing (`E0101` wrong role, `E0102` malformed casing):

```ril
type HttpServer = .{ port: int }       -- OK: title-cased acronym PascalCase
let local_port = 8080                  -- OK: snake_case local binding
meta let MAX_RETRY = 3                 -- OK: SCREAMING_SNAKE_CASE constant
```

```ril
-- Rejected casing and resolution cases:
-- type HTTPServer = .{ port: int }    -- Error [E0102]: acronym must be title-cased ('HttpServer')
-- let badCamel = 1                    -- Error [E0102]: mixed camelCase prohibited
-- let user__name = "Ada"              -- Error [E0102]: consecutive underscores prohibited
-- meta let max_retry = 3              -- Error [E0101]: 'meta let' requires SCREAMING_SNAKE_CASE
-- type user_doc = .{ id: int }        -- Error [E0101]: type identifier must be PascalCase
-- let Some(USER_ID) = Some(1)         -- Error [E0103]: uppercase identifier in pattern binding position
-- meta let MAX_RETRY = 4              -- Error [E0203]: duplicate declaration in same scope
-- let ghost = missing_name            -- Error [E0204]: unresolved identifier
-- type A { Dup }; type B { Dup }; let _ = Dup -- Error [E0206]: ambiguous constructor; write 'A::Dup'
-- let _ = 1; let bad_wild = _         -- Error [E0322]: '_' cannot be read as an expression
```

| Casing | Syntax & roles |
| :--- | :--- |
| `PascalCase` | Single `[A-Z]` (`T`, `M`) or `_`-free title-cased words (`UserId`, `HttpServer`, `Sha256`; no `HTTPServer`, `E0102`). Used for types, variants, nominal constructors, `eff`, `sub`/modules, and type/mode/tail generic parameters |
| `ValueName` (`SnakeCase` / `UnderscoreName`) | Lowercase `_`-separated (`local_port`, `_unused`). Used for locals, parameters, `fn`, `meta fn`, fields, effect ops, static value parameters, and file path segments |
| `ScreamingSnakeCase` | Uppercase with `_` or $\ge 2$ chars (`PI`, `UTF8`, `N_MAX`). Reserved exclusively for `meta let` constants (`E0101` on `let`/other declarations; `E0103` in patterns) |
| `Wildcard` (`_`) | Discard binding/pattern only (`E0322` if read as an expression) |

- **Name resolution (`E0203`, `E0204`, `E0206`)**: Duplicate same-scope declarations fail `E0203`; inner scopes may shadow outer non-protected bindings, while `Type` and `Super` cannot be redeclared or shadowed (`E0203`). Unresolved names fail `E0204`. Ambiguous unqualified variant constructors from multiple sums fail `E0206` (qualify as `SumA::Tag`).

```ebnf
Identifier         ::= PascalCase | ValueName | ScreamingSnakeCase
ValueName          ::= SnakeCase | UnderscoreName
PascalCase         ::= [A-Z]
                     | [A-Z] [a-z0-9]* [a-z] [a-z0-9]* { [A-Z] [a-z0-9]+ } [ [A-Z] ]
SnakeCase          ::= [a-z] { [a-z0-9] } { "_" [a-z0-9]+ }
ScreamingSnakeCase ::= [A-Z] [A-Z0-9]+ { "_" [A-Z0-9]+ }
                     | [A-Z] { [A-Z0-9] } "_" [A-Z0-9]+ { "_" [A-Z0-9]+ }
UnderscoreName     ::= "_" [a-z] { [a-z0-9] } { "_" [a-z0-9]+ }
Wildcard           ::= "_"
PathSegment        ::= PascalCase [ GenericArgs ]
QualifiedName      ::= { "Super" "::" } { PathSegment "::" } Identifier
```

### Keywords

The following 29 reserved syntax keywords cannot be used as identifiers or field labels (`E0113`):

```text
as       break    continue eff      else     false    fn       for
if       infer    let      match    meta     mut      new      pkg
pub      ref      return   sub      true     type     typeof   use
var      via      where    while    with
```

- **Protected Names (`bool`, `int`, `f64`, `str`, `bytes`, `never`, `Type`, `Super`)**: Primitive type names cannot be used as identifiers or field labels (`E0113`), `Type` and `Super` cannot be redeclared or shadowed (`E0203`), and bare type names in runtime value expressions fail `E0319` (write `<int>`, `<never>`).
- **Contextual Identifiers (`opaque`, `nominal`, `ril`, `io`, `fiber`, `capture`, `up`)**: Ordinary `SnakeCase` identifiers in bindings, parameters, paths, and fields (`let opaque = true`, `let fiber = 1`, `use ril/io`). Recognized contextually only in `opaque type`, `nominal type`, `use ril/...`, `@io`, `@fiber`, `&capture`, and `&up` / `&up(...)`.

```ril
let opaque = true                      -- OK: contextual outside 'opaque type'
let fiber = 1                          -- OK: contextual outside @fiber
-- let where = 1                       -- Error [E0113]: reserved keyword
-- let pkg = "core"                    -- Error [E0113]: reserved keyword
-- let via = 1                         -- Error [E0113]: reserved keyword
-- type BadField = .{ fn: bool }       -- Error [E0113]: reserved keyword as field label
-- let int = 0                         -- Error [E0113]: primitive type name
```

### Numeric Literals

Ril has two numeric types: arbitrary-precision signed `int` and IEEE-754 binary64 `f64`, with no width suffixes.

```ril
let big   = 1_000_000_000_000_000_000_000_000_000_000
let mask  = 0xFF_00
let ratio = 3.14159e-2

-- Rejected:
-- let bad_hex = 0x                    -- Error [E0111]: incomplete hex literal
-- let bad_suf = 42u8                  -- Error [E0111]: numeric suffixes are not supported
-- let bad_inf = 1.0e999               -- Error [E0326]: f64 literal overflows finite binary64
```

- Malformed digits, trailing `_`, or invalid suffixes fail `E0111`; `f64` overflow beyond finite binary64 fails `E0326`.
- Immediately after `.` or `?.`, decimal digits lex as individual `TupleIndex` tokens rather than `FloatLiteral` (`nested.0.1`).

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

### Text and Byte Literals

`str` holds valid UTF-8 scalar sequences; `bytes` holds immutable byte sequences (`0..=255`).

```ril
let host      = "ril.dev"
let port      = 443
let url       = "https://{host}:{port}/v1"
let raw_path  = #"C:\data\ril"#
let raw_quote = ##"contains "# and {literal_braces}"##
let magic     = bytes"\x89PNG\r\n\x1a\n"
let http_line = bytes#"GET / HTTP/1.1"#
assert(url == "https://ril.dev:443/v1" && len(magic) == 8 && len(http_line) == 14)
```

```ril
-- Rejected text and byte literals:
-- let bad_unterm = #"unterminated"    -- Error [E0107]: requires closing '"#'
-- let bad_esc    = "\q"               -- Error [E0108]: unknown escape
-- let bad_uni    = "\u{D800}"         -- Error [E0109]: UTF-16 surrogate is not a Unicode scalar
-- let bad_byte   = bytes"λ"           -- Error [E0110]: non-ASCII byte literal character
-- let bad_raw_b  = bytes#"λ"#         -- Error [E0110]: non-ASCII raw byte literal character
-- let bad_interp = "val={}"           -- Error [E0112]: empty interpolation expression
```

- **Interpolation (`E0112`, `E0301`)**: `"{expr}"` inside `"..."` accepts `str`, `int`, `f64`, or `bool` (`E0301` otherwise; `E0112` on empty `{}` or malformed braces; `{{` and `}}` escape literal braces).
- **Strings (`E0107`–`E0109`)**: `"..."` is single-line (`E0107` on newline/EOF) with escapes `\\`, `\"`, `\n`, `\r`, `\t`, `\0`, `\u{H+}` (1–6 hex digits; `E0109` on surrogates or `> 0x10FFFF`).
- **Raw strings (`E0107`)**: Open with $k \ge 1$ `#` tightly before `"` and close at the first `"` tightly followed by $k$ `#`; multiline (`CRLF -> LF`) with no escapes or interpolation.
- **Bytes (`E0110`)**: `bytes"..."` accepts single-line ASCII `0x20..0x7E` plus `\\`, `\"`, `\n`, `\r`, `\t`, `\0`, `\xHH` (2 hex digits). Raw `bytes#"..."#` admits multiline ASCII (`0x09`, `0x0A` with `CRLF -> LF`, `0x20..0x7E`) with no escapes.

```ebnf
StringLiteral     ::= '"' { StringCharacter | EscapeSequence | Interpolation } '"'
RawStringLiteral  ::= "#" { "#" } '"' { RawCharacter } '"' "#" { "#" }
ByteStringLiteral ::= 'bytes"' { ByteCharacter | ByteEscape } '"'
                    | "bytes" RawByteLiteral
RawByteLiteral    ::= "#" { "#" } '"' { RawByteCharacter } '"' "#" { "#" }
Interpolation     ::= "{" Expression "}"
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
                 | TypeValueType
                 | "(" TypeExpression ")"
                 | "<" Expression ">"
ResultType     ::= "!<" TypeExpression "," TypeExpression [ "," ] ">"
TypeReference  ::= QualifiedName [ GenericArgs ]
```

### Value Types

`bool`, `int`, `f64`, `str`, `bytes`, `()`, and `never` have no object identity and copy logically by value (implementations may share immutable backing buffers transparently).
- Value types forbid `ref`, `mut`, and `^mut` in bindings, record fields, collection elements, and `ref`/`^mut` expressions (`E0402`), and in parameters/call markers (`E0401`).

```ril
let a = "hello"
let b = a                              -- Value copy
-- let ref bad_ref = a                 -- Error [E0402]: value type 'str' forbids 'ref'
-- fn bad_param(mut n: int) -> () {}   -- Error [E0401]: value type 'int' forbids 'mut' parameter
```

### Shared Object Types

Records (`.{...}`), nonempty tuples `(A, B)`, arrays `[M]T`, maps `[K: M V]`, `Set<T>`, and sum instances have automatically reclaimed object identity (implementations need not heap-allocate objects whose identity or lifetime can be proven local). Shared-object status permits aliasing of immutable snapshots (`let`) and explicit shared writable bindings (`^mut`), never implicit shared mutation.

### Record Types and Open Record Tails

Record types, values, patterns, and mapped types uniformly use `.{...}`. Record fields may carry slot/access `MemberMode` modifiers (`var`, `mut`, `^mut`, `ref`, `var mut`, `var ^mut`, `var ref`), inferred `via` modes, or a static `MemberMode` expression `M` (`E0356`).

```ril
type WithId<R> = .{ id: int, ..R }
nominal type ServerCfg = .{ host: str, port: int = 8080, var retries: int = 3 }

fn get_id(item: .{ id: int, .. }) -> int { item.id }

let cfg = ServerCfg.{ host: "ril.dev" }
assert(get_id(.{ id: 7, active: true }) == 7)
assert(cfg.port == 8080 && cfg.retries == 3)
assert(get_id(inner(cfg) |> \_ -> .{ id: 1 }) == 1)
```

```ril
-- Rejected field, tail, and default cases:
-- type BadDup = .{ id: int, id: int }                  -- Error [E0210]: duplicate field label
-- type BadOverlap = WithId<.{ id: str }>               -- Error [E0212]: tail overlaps 'id'
-- type BadTail = WithId<int>                           -- Error [E0306]: tail requires structural record
-- let bad_extra: .{ id: int } = .{ id: 1, x: 2 }       -- Error [E0302]: unexpected field 'x'
-- let bad_miss: .{ host: str, port: int } = .{ host: "a" } -- Error [E0307]: missing field 'port'
-- let bad_unknown = cfg.email                          -- Error [E0336]: unknown field 'email'
-- let bad_dyn = cfg["host"]                            -- Error [E0324]: dynamic bracket index on record
-- let bad_mode: .{ var x: int } = .{ x: 1 }            -- Error [E0357]: incompatible member mode

-- type BadAliasDef = .{ port: int = 8080 }             -- Error [E0359]: alias forbids field defaults
-- nominal type BadNested = .{ inner: .{ x: int = 1 } } -- Error [E0359]: default only on root fields
-- nominal type BadMutDef = .{ mut items: []int = [] }  -- Error [E0404]: writable field forbids default
-- nominal type BadFwd = .{ a: int = b, b: int = 1 }    -- Error [E0408]: forward field reference
-- eff Rng { fn next() -> int }
-- nominal type BadImpure = .{ seed: int = Rng::next() }-- Error [E0409]: field default must be pure
```

- **Closed records**: Exact field set, order irrelevant (`E0210` duplicate, `E0307` missing, `E0302` unexpected, `E0336` unknown field read, `E0324` dynamic `rec[k]`).
- **Open record tails (`..R` / `..`)**: Opens structural records (row polymorphism) in generic constraints, aliases, or direct callable parameters (`E0306` on non-record/nominal—unwrap via `inner`/`Unwrap<T>`; `E0212` on label overlap; `E0357` on mode mismatch). Anonymous `..` is permitted only in generic constraints and direct callable parameters (and transparent aliases expanded there); concrete storage and return types require closed records or explicit generic tail parameters (`E0344`).
- **Root field defaults (`= expr`)**:
  - Allowed only on root fields of `.ril` `NominalTypeDecl` / `OpaqueTypeDecl` records (`E0359` on aliases, nested/anonymous/parameter/sum records; `E0901` in `.d.ril`). Root fields of `.ril` nominal/opaque records also admit `meta(...)` attributes.
  - Allowed only on plain or `var` fields—forbids `mut`/`^mut`/`ref`/`via` and parametric `StorageModeExpression` (`E0404`), self/forward references (`E0408`), and impure expressions (`E0409`).
  - At construction (`ServerCfg.{ host: "ril.dev" }`), explicit fields evaluate left-to-right first, then omitted defaults in declaration order.

```ebnf
RecordType      ::= ".{" [ RecordFieldList ] "}"
RecordFieldList ::= RecordTail
                  | RecordField { "," RecordField } [ "," RecordTail ] [ "," ]
RecordField     ::= { MetaAttr } [ RecordFieldMode ] FieldLabel ":" TypeExpression [ "=" Expression ]
RecordFieldMode ::= MemberMode | "via" | StorageModeExpression
FieldLabel      ::= ValueName
RecordTail      ::= ".." [ PascalCase ]
MemberMode      ::= "var" [ "mut" | "^mut" | "ref" ]
                  | "mut" | "^mut" | "ref"
```

### Array, Map, Set, and Tuple Types

Arrays `[M]T`, maps `[K: M V]`, and `Set<T>` are shared-object collections with automatically reclaimed identity; tuples `()` and `(A, B, ...)` are fixed-arity immutable aggregates.

```ril
let xs: []int = [10, 20, 30]
let mut table: [str: int] = ["ok": 200]
table["not_found"] = 404
let pair: (int, str) = (1, "one")
assert(xs[0] == 10 && table?["ok"] == Some(200) && pair.1 == "one")

-- Rejected:
-- let bad_map_read = table["ok"]      -- Error [E0352]: map read requires safe 'table?["ok"]'
-- let bad_idx = pair.2                -- Error [E0312]: tuple index out of bounds
-- type BadKey = [f64: int]            -- Error [E0328]: 'f64' cannot be a map/set key
-- type BadElem = [var][]int           -- Error [E0356]: element mode forbids 'var'
```

- **Element modes (`E0356`)**: Plain `[]T` / `[K: V]` hold deeply immutable elements. Element modes admit `mut`, `^mut`, `ref`, `via`, or a static `MemberMode` expression without `var` (`E0356`).
- **Keys & indexing (`E0328`, `E0352`)**: Map keys `K` and `Set<T>` elements require structural equality (`E0328`). Map reads use safe `m?[k] -> ?V` (`E0352` on `m[k]` reads or `m[k] += v`); `m[k] = v` inserts/updates. Lengths and indices have type `int`.
- **Tuples (`E0312`)**: Zero-element `()` or $\ge 2$ elements `(A, B)`. `(T)` is grouping, never a 1-tuple. Tuple slots are strictly immutable; use records for mutable multi-field data.

```ebnf
ArrayType             ::= "[" [ ElementAccessMode ] "]" TypeExpression
ElementAccessMode     ::= "mut" | "^mut" | "ref" | "via" | StorageModeExpression
StorageModeExpression ::= { "Super" "::" } { PathSegment "::" } ( PascalCase | ScreamingSnakeCase )
MapType               ::= "[" TypeExpression ":" [ ElementAccessMode ] TypeExpression "]"
TupleType             ::= "(" ")"
                        | "(" TypeExpression "," TypeExpression { "," TypeExpression } [ "," ] ")"
```

### Sum Types and Variant Spreading

Each sum variant declares either a unit tag or **one** payload type (multiple items inside `(...)` form a tuple payload; empty `()` is unit payload `()`).

```ril
pub type Shape {
    Origin
    Circle(f64)
    Rect(f64, f64)
    Polygon(.{ vertices: [](f64, f64), closed: bool })
}

let s1 = Shape::Origin
let s2 = Shape::Circle(5.0)
let s3 = Shape::Rect(10.0, 20.0)
let s4 = Shape::Polygon(.{ vertices: [(0.0, 0.0)], closed: true })
let s5 = Shape::Rect((3.0, 4.0))       -- Single tuple matches Rect(f64, f64)
let opt: ?int = 99 |> Some
let res: !<int, str> = 42 |> Ok
assert(opt == Some(99) && res == Ok(42))

-- Rejected:
-- let _ = Shape::Origin()             -- Error [E0338]: unit variant takes no payload
-- type BadSingleRes = !<int>          -- Error [E0120]: '!<T, E>' requires both Ok and Err types
```

- **Construction & sugars**: Unit variants stand alone (`None`, `Origin`; `Origin()` fails `E0338`). Payload variants use tight `(...)` (`Ok(42)`, `Ok()`, `Rect(10.0, 20.0)`; named labels fail `E0339`, `mut` args fail `E0406`) and bare payload-variant names act as `fn(Payload) -> Sum` (`42 |> Ok`). `?T` ≡ `Option<T>`; `!<T, E>` ≡ `Result<T, E>`.
- **Payload modes**: Single-payload constructors (`Some(ref x)`, `Some(^mut x)`, `Some(new x)`) restrict the outer sum's authority to the payload's mode (`E0522`/`E0510` on unshared `mut`/`[mut]Sum`). Multi-arg tuple payloads (`Pair(a, b)`) have immutable slots (`E0535` on `ref`/`^mut`).
- **Extensible sums (`..`)**: Trailing `..` marks a sum open to future variants outside its defining `pkg`, requiring a `_` wildcard arm in `match` expressions outside that package (`E0303`).

```ebnf
SumTypeDecl        ::= ( TypeDeclHead | OpaqueTypeHead ) [ UseCleanupClause ] "{" [ VariantDeclList ] "}"
VariantDeclList    ::= VariantDeclItem { Separator VariantDeclItem } [ Separator ]
VariantDeclItem    ::= VariantSpread | VariantDecl
VariantSpread      ::= ".." TypeReference
VariantDecl        ::= { MetaAttr } PascalCase [ "(" [ VariantPayloadType ] ")" ]
                     | ".."
VariantPayloadType ::= TypeExpression { "," TypeExpression } [ "," ]
UseCleanupClause   ::= "use" "(" ValueName ")"
```

#### Sum Variant Spreading and Subset Conversion

`..SubType` splices another accessible transparent sum's variants into a superset sum, establishing static sum inclusion $Sub \preceq_{\text{sum}} Sup$ when `Sup` is transparent (or inside an `opaque` sum's defining scope; sealed outside with `E0308` / `E0301`).

```ril
pub type DbErr   { Deadlock; ConnLost(str) }
pub type AuthErr { MissingToken; Expired }
pub type ApiErr  { ..DbErr; ..AuthErr; BadInput(str) }
-- type ConflictErr { ..DbErr; ConnLost(int) } -- Error [E0213]: conflicting payload for 'ConnLost'

fn handle_err(err: ApiErr) -> new (int, str) {
    match err {
        DbErr as db     -> (503, match db { Deadlock -> "retry"; ConnLost(h) -> h })
        ..AuthErr       -> (401, "unauthorized")
        BadInput(field) -> (400, field)
    }
}

fn widen_demo(e: DbErr) -> ApiErr { e as ApiErr } -- OK: DbErr <= ApiErr
```

- **Spread checks**: Fails `E0306` on non-sum, `E0308` on sealed/open sum, `E0313` on cycles, and `E0213` on conflicting payload shapes for the same tag (including unit `Ping` vs unit-payload `Ping()`); identical tags with equivalent payloads deduplicate cleanly.
- **Three inclusion operations** (when $Sub \preceq_{\text{sum}} Sup$):
  1. **Postfix `?` widening**: `sub_res?` widens `Err(sub_err)` to `Sup` in a function returning `!<T, Sup>`.
  2. **Explicit widening (`e as Sup`)**: Re-wraps `Sub` into `Sup` (`E0301` otherwise).
  3. **Pattern subset matching (`Sub as binder`, `..Sub`)**: Matches any variant belonging to `Sub`.

| Source authority of `e` | Subset re-wrap (`Sub as x` / `e as Sup`) provenance rule |
| :--- | :--- |
| Deeply immutable `e` (or immutable-only payloads) | Produces an ordinary deeply immutable value |
| `new`-qualified | Hands off and ends the source path (`E0549`); produces `new` target sum |
| Shared writable `^mut` (with mutable payload members) | Requires `^mut` marker (`Sub as ^mut x` / `(^mut e) as Sup`, `E0510`); returning records `&return(^mut src)` |
| `ref` / `mut` access (with live/mutable payload members) | Scoped access bounded by source's valid scope; forbids persistent `let ref` (`E0543`) and root `-> ref(src)` (`E0545`); contained return records `&return(ref src)` |

### Nominal, Type Alias, and Opaque Types

Ril defines four `.ril` type forms alongside `.d.ril` foreign opaque handles:

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

let uid = UserId(42)
assert(inner(uid) == 42 && inner(Disconnected) == ())
let mut c0 = open_raw()
let mut c1 = dial(new c0, 3)
close_conn(new c1)
```

```ril
-- Rejected nominal, alias, and opaque cases:
-- let _ = dial(new c0, 4)             -- Error [E0549]: 'c0' ended at handoff
-- let bad_nom: OrgId = UserId(1)      -- Error [E0305]: distinct nominal types
-- pub type MissingEq .{ id: int }     -- Error [E0124]: missing '=' in type declaration
-- type Cyc = Cyc                      -- Error [E0313]: cyclic transparent type alias
-- let bad_peek = c1.fd                -- Error [E0308]: opaque representation sealed outside defining scope
```

| Form | Syntax | Identity & representation |
| :--- | :--- | :--- |
| Transparent alias | `type Point = .{ x: f64, y: f64 }` | Type-equivalent to target everywhere (`E0313` cycles; forbids `meta(...)` `E0708` and defaults `E0359`) |
| Nominal type / marker | `nominal type Marker`<br>`nominal type UserId = int`<br>`nominal type Req = .{ k: str }` | Distinct type everywhere (`E0305`); public representation. Unit `Marker` stands alone; non-records use `UserId(42)` / `Pair(1, 2)` and bare non-record nominal names act as `fn(Payload) -> Nominal` (`42 \|> UserId`, exempt from `E0319`); records use `Req.{ k: "a" }` (`E0338` on mismatch). Unwrap via `inner(w)` |
| Scope-opaque type (`.ril`) | `opaque type Token = str` | Interconvertible with representation inside exact defining `sub` or root file (`<Token> != <str>`); sealed outside, including child/parent `sub`s (`E0301`, `E0308`). Bodyless `.ril` `opaque type` requires registered built-in (`E0902`) |
| Sum type | `type Res<T, E> { Ok(T); Err(E) }` | Closed or extensible variant type (`opaque` seals construction, widening, and matching outside defining scope, `E0308`) |
| Foreign opaque handle (`.d.ril`) | `pub opaque type HostFd use(close)` | Exclusive, non-duplicable host handle (`E0907` access, `E0908` snapshot/`^mut` signature); forbids `clone`, `derive`, `==`, freezing, `var mut`, and collections; admits `new`, `let mut`, `mut`, `ref`, `use` |

```ebnf
TypeDecl        ::= TypeDeclHead "=" ( TypeExpression | TypeFunctionExpr )
NominalTypeDecl ::= NominalTypeHead [ UseCleanupClause ] [ "=" TypeExpression ]
OpaqueTypeDecl  ::= OpaqueTypeHead [ UseCleanupClause ] [ "=" TypeExpression ]
TypeDeclHead    ::= { MetaAttr } [ Visibility ] "type" PascalCase [ GenericParams ]
NominalTypeHead ::= { MetaAttr } [ Visibility ] "nominal" "type" PascalCase [ GenericParams ]
OpaqueTypeHead  ::= { MetaAttr } [ Visibility ] "opaque" "type" PascalCase [ GenericParams ]
LocalTypeDecl   ::= TypeDecl | NominalTypeDecl | OpaqueTypeDecl | SumTypeDecl
```

### Deep Immutability

Plain `let`, `var`, plain parameters, and plain collection elements hold **deeply immutable snapshots**: no surviving writable alias (`mut` / `^mut`) or live `ref` view may reach the stored graph (`E0535`). On a frozen snapshot, declared `var`/`mut`/`ref` member modes stay inactive (`E0520` on write).

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
-- let mut bad_holder = .{ mut cb: \-> { shared.count += 1; shared.count } } -- Error [E0510]: retains '^mut'
assert((holder.cb)() == 2)
-- let _ = clone(ref holder)           -- Error [E0530]: cannot clone mutable closure authority
```

- **`clone(value)` / `clone(ref live)`**: Deep-copies an ordinary `SharedObject` graph (preserving internal aliases and cycles) into an isolated `new T`.
- **Clonability restrictions**: Fails `E0301` on value-type roots, callables, or graphs containing `.d.ril` `opaque` handles, `Scope`, `Task`, `Sender` (use `Channel::clone`), `Receiver`, or `Draft`; fails `E0530` on live/mutable closure environments.

### Type Identity and Subtyping

Ril has **no implicit numeric widening** and **no structural width subtyping** on closed records (`E0301`).

```ril
fn diverge() -> never { panic("stop") }

let n: int = diverge()                         -- OK: never <: T
let opt: ?int = if true { Some(1) } else { diverge() }
let ok_cb: fn(int) @io -> int = \x -> x        -- OK: pure fn <: @io fn
-- let bad_num: f64 = 1                        -- Error [E0301]: no implicit int -> f64 widening
-- let bad_rec: .{ x: int } = .{ x: 1, y: 2 } -- Error [E0302]: closed records have no width subtyping
```

Subtyping $S <: T$ holds **only** for:
1. **Type equivalence** ($S \equiv T$): expands transparent `type A = B` aliases, plus bidirectional `A` $\leftrightarrow$ `Rep` for `.ril` `opaque type A = Rep` inside its exact defining `sub` or root file.
2. **Bottom type**: `never <: T` for every well-formed `T`.
3. **Covariant immutable wrappers**: `?S <: ?T` when $S <: T$; `!<S1, E1> <: !<S2, E2>` when $S_1 <: S_2 \land E_1 <: E_2$ (mutable/invariant containers require `S ≡ T`).
4. **Callable subtyping** (via `MatchCallable`): accepts broader parameter types, returns a narrower result type, matches concrete access modes and return provenance, and stays within bounded effect/state sets.

### Complete Provenance and Required Annotations

Access modes, sources, state writes, environment captures, and effects are purely static judgments verified modularly across call boundaries; they have no observable runtime representation and require no runtime tracking or dispatch.

Named functions spell their minimal `@Eff` and non-pure state/provenance clauses (`&mut`, `&^mut`, `&capture`, `&up(...)`, `&return(...)`); anonymous closures infer complete signatures automatically.

### Access Mode Inference with via and infer

`via` binds static access-mode parameters over parameter/member schemas; `-> infer T` derives the return mode (`plain`, `ref(...)`, `^mut(...)`, `new`) and `&return(...)` provenance while keeping data type `T` explicit:
- Named callable declarations writing `-> infer T` require an explicit `via` parameter (root `via x: U` or composite `[via]U` / `[K: via V]` / `.{ via f: U }`) in that callable's own parameter list (`E0412`).
- In a `CallableType` parameter (`via cb: fn(...) ... -> infer T` or `cb: fn(via A) ... -> infer T`) or a closure inside a `via` template, `-> infer T` and `let via` bind to the callable's own or enclosing `via` parameter (`E0412` if none is in scope, including standalone `via`-field types).

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
let mut handed = relay(new live)
handed.count += 10
assert(plain.count == 1 && handed.count == 12)
-- fn bad_infer(x: Cell) -> infer Cell { x }    -- Error [E0412]: 'infer' requires 'via' parameter
-- fn bad_scalar(via n: int) -> int { n }       -- Error [E0550]: redundant 'via' on concrete value type 'int'
-- Published interface: fn read(via c: Cell) -> int; restricting to '&mut' breaks baseline -> Error [E0552]
```

#### Member Modes and Implicit Schema Parameters

`via` in composite parameter schemas (`[via]T`, `[K: via V]`, `.{ via item: T }`) binds an implicit member-mode parameter from the caller's schema.

Ordinary access and replacement use the received schema; concrete member/element modes match supplied modes exactly (`E0357`). `new`-qualified reception selects access modes (`plain`, `mut`, `^mut`, `ref`, with `ref` slots requiring explicit `ref` expressions) for `new` subgraphs while existing-source modes stay fixed; it never synthesizes `var` slot replaceability on anonymous records (`E0357`).

#### Inference Domains and Signature Completion

A `via x: T` parameter admits modes from `{plain, ref, mut, ^mut, new}` compatible with `T` and all body uses. Writing `via` on a concrete value type (`via n: int`, `via s: str`) fails `E0550`.

Inside a `via` function, concrete `&mut` / `&^mut` / `&return` clauses implied solely by `via` instantiations are recorded in the inferred template interface automatically without redundant header annotations.

#### Preserving Reception and Forwarding

Within a lexical `via` template, `let via y = expr` preserves the exact instantiated access mode and `new`-subgraph/contained-source provenance of a `via`-dependent expression (`E0550` if `expr` has a fixed non-dependent mode).

A target's expected writable mode cannot manufacture `new` qualification for an existing immutable or `ref` source; concrete calls to non-`via` parameters still require explicit `mut` / `ref` / `^mut` / `new` argument markers (`E0405`).

#### Lexical Mode Templates and Closures

Closures inside a `via` function may reference enclosing `via` bindings; captured schemas and `-> infer` return specifications specialize per outer mode instantiation while enforcing standard capture, scope-confinement, and single-use `new` handoff rules.

#### Inferred Interfaces and Callable Families

In higher-order parameter types, `fn(via T) @& -> infer R` opens mode polymorphism independently of `@&` effect/state openness. Exported `via` functions retain normalized mode-to-signature summaries in module metadata; restricting accepted modes or weakening result guarantees against a published interface baseline fails `E0552`.

### Functional Updates via Derive

`derive(base, \mut draft -> { ... })` (typically piped as `base |> derive \mut draft -> { ... }`) performs path-targeted updates on a deeply immutable `SharedObject` snapshot, returning a new deeply immutable `T` while leaving `base` unchanged (implementations may structurally share unchanged immutable subgraphs).

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
-- let _ = base |> derive \mut d -> { leak = Some(\-> d.profile.email) } -- Error [E0607]: Draft escapes derive closure
```

| `derive` rule | Requirement |
| :--- | :--- |
| Root eligibility (`E0536`, `E0308`) | `base` must be a deeply immutable `SharedObject` (including accessible `nominal` and in-scope `.ril` `opaque` shared objects; sealed `.ril` `opaque` roots fail `E0308`); value types, foreign `.d.ril` `opaque` handles, and live `mut`/`^mut`/`ref` roots fail `E0536` |
| `Draft<T>` path operations | Confined `mut Draft<T>` paths permit `d.field = v` (regardless of `var`), tuple-slot updates `d.0 = v`, `mut` collection operations (`d.tags \|> mut Array::push(...)`), `inner(mut d)` on accessible nominal wrappers, and `match d { Tag(mut p) -> ... }` in-place variant payload updates |
| `Draft<T>` confinement (`E0607`) | `Draft<T>` is bound to the `derive` closure activation; draft handles, derived `ref`/`mut` paths, and capturing closures cannot escape the `derive` closure (`E0607`) |
| Inserted values (`E0535`) | Assigned values must be deeply immutable or newly allocated inside the `derive` closure and free of surviving outside writers (`E0535`) |
| Fixed shape (`E0336`, `E0312`) | Preserves record fields, tuple arity, and active sum tags of `T`; forwards the `derive` closure's effects and outer state obligations |

```ril
nominal type Bag = []int
let t2 = (1, "a") |> derive \mut d -> { d.0 = 2 }
let b2 = Bag([1, 2]) |> derive \mut d -> { inner(mut d) |> mut Array::push(3) }
assert(t2 == (2, "a") && inner(b2) == [1, 2, 3])
```

### Generic Parameters, Defaults, and Static Kinds

Declarations admit abstract type parameters (`T`), compile-time value parameters (`cap: int`), and member-mode parameters (`M: MemberMode`). Type declarations (`type`, `nominal type`, `opaque type`, `TypeFunctionExpr`) admit trailing generic defaults (`E0316` non-trailing, `E0320` forward reference; prohibited on `fn`/`meta fn`, `E0317`).

```ril
fn add<T: int | f64>(a: T, b: T) -> T { a + b }
assert(add(2, 3) == 5 && add(1.5, 0.5) == 2.0)

type Positive = \n: int -> if n > 0 { <()> } else { <never> }
type AtLeast  = \n: int, lo: int -> if n >= lo { <()> } else { <never> }
type Chunk<T = int, cap: int |> Positive |> AtLeast<1> = 64, M: MemberMode = mut> = .{ M data: []T }
type DefaultChunk = Chunk<>
type FrozenChunk  = Chunk<int, 1, let>          -- OK: 'let' selects plain immutable member mode
```

```ril
-- Rejected generic declarations and arguments:
type WrongCheck = \n: int -> <str>
type Checked<n: int |> WrongCheck> = int
-- type BadCheck = Checked<1>                   -- Error [E0306]: static value check returns <str>, not <()>/<never>
-- type BadOrder<T = int, U> = (T, U)           -- Error [E0316]: non-trailing generic default
-- fn bad_fn_def<T = int>(x: T) -> T { x }      -- Error [E0317]: generic defaults prohibited on functions
-- type BadGenFwd<A = B, B = int> = (A, B)      -- Error [E0320]: forward generic default reference 'B'
-- type BadChunk = Chunk<int, 0>                -- Error [E0323]: fails static check 'Positive'
-- type BadKind = Chunk<int, str>               -- Error [E0323]: type supplied to static value parameter
-- type BadUnion = int | str                    -- Error [E0318]: untagged union cannot be a storage type
-- type BadArity = Option<int, str>             -- Error [E0340]: generic arity mismatch
-- let bad_empty = []                           -- Error [E0344]: element type undetermined
-- fn dyn_cap(n: int) -> () { let _: Chunk<int, n> = .{ data: [] } } -- Error [E0814]: non-static value argument
```

- **Closed type sets (`T: int | f64`)**: Every member is checked at definition time (`E0301`), each call instantiates `T` to one concrete type (`E0306`), and `match <T>` over all members is exhaustive (`E0304` on redundant `_`). Bare untagged unions or literal types fail `E0318`.
- **Static type checks (`T |> Check<Args>`)**: Passes `T` first; holds iff $T \not\equiv \text{never} \wedge \text{Check}\langle T, \text{Args} \rangle \equiv T$ (`E0301`, `E0306`).
- **Static value checks (`cap: int |> Positive`)**: Runs after kind checking and substitution; accepts `<()>`, rejects `<never>` (`E0323`), and fails `E0306` on any other type value. `Key<T>` (`val |> Key<T>` $\equiv$ `Key<val, T>`) validates coordinates of `T`.
- **Strict parameter kinds (`E0306`, `E0323`, `E0814`, `E0340`, `E0344`)**: Ordinary values and type values cannot supply type parameters (`E0306`; write `typeof e`). Type syntax adapts one-way to a declared `Type<T>` static value parameter. `Reflect::MemberMode` re-exports prelude `MemberMode`.

```ebnf
GenericParams         ::= "<" GenericParamDecl { "," GenericParamDecl } [ "," ] ">"
GenericParamDecl      ::= TypeParamDecl | StaticValueParamDecl | ModeParamDecl
TypeParamDecl         ::= PascalCase [ TypeConstraint ] [ "=" TypeExpression ]
TypeConstraint        ::= [ ":" TypeKind ] { "|>" PipelineConstraint }
TypeKind              ::= TypeSetKind | "Type" | RecordConstraint
TypeSetKind           ::= TypeSetMember "|" TypeSetMember { "|" TypeSetMember }
TypeSetMember         ::= PrimitiveType | TypeReference | ResultType | "?" TypeSetMember
                        | TupleType | ArrayType | MapType | RecordType
PipelineConstraint    ::= QualifiedName [ GenericArgs ]
StaticValueParamDecl  ::= ValueName ":" TypeExpression { "|>" PipelineConstraint } [ "=" Expression ]
RecordConstraint      ::= ".{" RecordConstraintField { "," RecordConstraintField } "," RecordTail [ "," ] "}"
                        | ".{" RecordTail [ "," ] "}"
RecordConstraintField ::= [ RecordFieldMode ] FieldLabel ":" TypeExpression
ModeParamDecl         ::= PascalCase ":" ModeKindReference [ "=" MemberModeLiteral ]
ModeKindReference     ::= [ "Reflect::" ] "MemberMode"
GenericArgs           ::= "<" [ GenericArg { "," GenericArg } [ "," ] ] ">"
GenericArg            ::= TypeExpression | Expression | MemberModeLiteral
MemberModeLiteral     ::= "let" | "var" [ "mut" | "^mut" | "ref" ] | "mut" | "^mut" | "ref"
```

### Type Definition Boundaries

Effects (`@Eff`), state clauses (`&mut`, `&up`), and open effect/state markers (`@`, `&`, `@&`) belong exclusively on `CallableType` arrows and function declarations:

```ril
-- type BadEff = @io                   -- Error [E0330]: effect is not a data type
-- type BadState = &mut                -- Error [E0331]: state clause is not a data type
-- type BadVar { Run(int) @io }        -- Error [E0332]: effect suffix on sum variant
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
J = (access, provenance, obligations, latent effects and state, confinement, normal-completion flow)

C |- A : Type                         well-formed data type
C |- a : Static(K)                    static argument of kind K
C |- A equiv B                        type equivalence
C |- A <: B                           subtyping
C |- Receive(actual, target)          mode and provenance reception
C |- MatchCallable(actual, expected)  callable compatibility
C |- e => T ; J                       bidirectional synthesis
C |- e <= T ; J                       bidirectional checking
C |- e <= TypeResult ; J              type-producing result checking
```

| Context component | Contents |
| :--- | :--- |
| `D` | Package (`pkg`) and module scopes, visibility/opacity, type `use` cleanup declarations, primitive/foreign signatures |
| `Delta` | Abstract type, static value, member-mode, and record-tail parameters |
| `Gamma` | Value bindings, slot/access modes, callable signatures, confinement scope tags |
| `Phi` | Declared generic constraints and static `match <T>` branch type facts |
| `F` | Source sets, active `new` paths, aliasing/exclusivity, `Result` inspection obligations |
| `q` | Phase: `TypeEval`, `MetaValue`, or `RunTime` |

### Type Formation and Binding

- **K-TYPE**: Primitives, abstract parameters in `Delta`, well-kinded generic applications, distinct-label records, arity-$0$ or $\ge 2$ immutable-slot tuples, valid-mode collections, complete `CallableType` signatures, `Type<A>`, and forward-evaluated computed types form valid types.
- **K-TYPE-TAIL**: `.{ fields L, ..R }` is well-formed iff `R` instantiates to a structural record tail whose labels are disjoint from `L` (`E0306` on non-record `R`, `E0212` on overlapping labels).

### Type Equivalence and Recursive Types

- **Alias expansion (`K-EQ`)**: `?T` ≡ `Option<T>`, `!<T, E>` ≡ `Result<T, E>`, and transparent `type A = B` aliases expand directly; cyclic transparent aliases without nominal or sum indirection fail `E0313`.
- **Structural & nominal identity (`K-EQ`)**:
  - Structural records compare equal up to field reordering when labels, types, and `MemberMode`s match.
  - Nominal, sum, and `opaque` types (`.ril` and `.d.ril`) compare by declaration identity and static argument equivalence (IEEE bits for `f64` with `-0.0 != 0.0` and NaNs agreeing; structural value equivalence for collections/records; equivalent target types for `Type<A>`).
- **Opacity scope**: Inside its exact defining `sub` or root `.ril` file, `opaque type A = Rep` converts bidirectionally with `Rep` while keeping `A`'s distinct identity in `Type<A>` and exported interfaces. Outside that exact scope (including child/parent `sub`s), value/construction mismatch fails `E0301` and representation access fails `E0308`.

### Subtyping, Reception, and Callable Compatibility

**`K-RECV` (`Receive`)** validates receiving a value's mode and sources into a target binding, parameter, element, or return schema:

| Target mode | Accepted input | Key diagnostics |
| :--- | :--- | :--- |
| Plain immutable | Plain deeply immutable value, or `new` result with freezable `new` subgraphs and deeply immutable existing-source boundaries | `E0535` (surviving writers or `ref` mode/sources) |
| Persistent `mut` (`let mut`, `mut` field, `[mut]T`) | Unshared writable authority or `new` subgraphs free of `^mut` constituents | `E0510` (unacknowledged alias), `E0522` (element mode escalation), `E0520` (immutable/`ref`) |
| Call-scoped `mut` parameter (`fn(mut p: T)`) | `mut` or `^mut` path under `mut path` / `\|> mut` | `E0406` (marker mismatch), `E0523`/`E0524` (call overlap) |
| Shared `^mut` (`let`/`var ^mut`, `^mut` field, `[^mut]T`) | Writable source with `^mut` acknowledgment on existing roots, or `new` `&up` closure retaining a `^mut` source | `E0510` |
| `let ref` / `var ref` | Pinned `let mut` source, non-`var` `ref` view, immutable shared object, or (`let ref` only) `new`-qualified composite / `&up(ref)` closure carrying live `ref` sources | `E0531` (`var`/`var ref` root), `E0543` (unanchored pure/immutable temporary), `E0604` (scope does not enclose `var ref`) |
| `new` target | `new`-qualified result or `new x` root handoff (ending `x`); chooses modes only for `new` subgraphs, preserving existing sources | `E0548`, `E0549` |
| `use [mut] x = expr` | Anchors `expr` in an implicit block cleanup slot, checked against $\max(M_{\text{body}}, M_{\text{clean}})$; exposes `ref` (or `mut`) in body | `E0541`, `E0548`, `E0520` |

- **`ref` reassignments & `ref` slots**: `var ref` reassignments and `[ref]T` / `[K: ref V]` / `.{ [var] ref f: T }` slots require `ref`-mode expressions (`ref expr` or an existing `ref` binding/parameter; bare plain/`mut` values fail `E0357`).
- **Mutable shared-object `ref` slots**: Writing into an existing mutable record or collection `ref` slot rejects local live or temporary `ref` views (`E0531` / `E0604` / `E0607`), while newly constructed `new` wrappers record `&return(ref x)`.

### Bidirectional Expression Checking

- **Synthesis & Checking (`K-EXPR`)**: Operands evaluate and check left-to-right.
  - Contextual expected types propagate inward to empty array/map literals (`[]`), anonymous closures (`\x -> ...`), sum constructors (`Ok(1)` under `!<int, str>`), and `if`/`match` arms (`E0344` if required type/static-value instantiation or fixed storage remains undetermined).

#### Anonymous Generalization and Fixed Storage

```ril
let identity = \x -> x
let read_id  = \r -> r.id
assert(identity(42) == 42 && identity("ril") == "ril")
assert(read_id(.{ id: 1, name: "a" }) + read_id(.{ id: 2, ok: true }) == 3)
-- var poly_slot = \x -> x              -- Error [E0344]: reassignable storage requires a fixed concrete type
```

- **Local generalization (`K-ANON`)**: Pure anonymous functions bound by local `let` generalize unresolved unconstrained parameters and open record-tail constraints, instantiating independently at each call site.
- **Multi-`?` error join**: When an unannotated closure has multiple `?` sites over `!<_, E_i>`, its inferred error type is the unique greatest sum $E_{\max} \in \{E_i\}$ under $\preceq_{\text{sum}}$ (`E0344` if none dominates and no contextual `CallableType` supplies the target).
- **Fixed concrete storage**: `var` slots, array/map elements, record fields, and escaping runtime values require fixed concrete schemas (`E0344`).

### Structural Joins and Normal Completion

- **K-JOIN**: Branches that never complete normally (`never` from `return`, `break`, `continue`, `panic`, `?`, `...`) contribute their prior side effects and obligations without constraining the join result type. Normally completing branches must join to a common type (`E0351` on incompatible types).
- **K-TYPE-RESULT**: In `TypeFunctionExpr` bodies, different static branches may return `Type<A>` and `Type<B>` values for distinct well-formed types `A` and `B`; closed evaluation yields the selected branch's single concrete type value.

### Generic Type Facts and Definition Checking

- **K-GEN**: Generic function bodies typecheck once at definition time against all admitted instantiations (`E0301` on unproved operations).
- **K-GEN-MATCH**: Transparent unguarded type-pattern decision trees (`\T -> match <T> { <int> | <f64> -> <T>; _ -> <never> }`) supply path-specific positive and negative type facts to constrained generic bodies.

### Authority, Calls, and Provenance Operations

- **K-CALL**: Call preparation evaluates explicit arguments left-to-right (then omitted defaults and parameter guards) and freezes the call-entry reachability graph.
  - It immediately ends any `new arg` source path (`E0549` on later arguments), checks aliasing exclusivity (`E0523`, `E0524`), and instantiates return sources (`ref(x)`, `^mut(x)`, `&return(...)`).
- **Pure Constant Sources**: Reading module/`sub`-level pure immutable constants (`let` or ordinary-valued `meta let`) introduces **zero** `&up` state or capture obligations.

### Recursive Summaries and Non-Circular Inference

- **K-FIX**: Mutually recursive functions and `via` mode families compute minimal consistent (least fixed-point) summaries over writes, captures, escapes, and unhandled effects.
  - `new` qualification, isolation, local state containment, and reachable authority use (`E0527` — e.g. self-forwarding `fn f(mut c: Cell) -> () { f(mut c) }`) require non-circular proofs.

### Phase Checking and Static Evaluation

- **K-PHASE**:
  - `TypeEval` and `MetaValue` run under the root step budget (`E0811` exhaustion; `E0830` failed `assert`; `E0831` `panic` or arithmetic defect).
  - Runtime values and storage cannot hold `Type<T>` values (`E0816`). `meta fn` returns, `meta let` constants, and `meta(...)` attributes must be type-value-free (`E0812` / `E0816`), callable-free (`E0816`), and `use`-resource-free (`E0816`) deeply immutable values (`E0813` on `@Eff` / `&State` on `meta fn`).
  - Direct saturated `meta fn` calls with static arguments (`E0814` on runtime arguments) evaluate at compile time in runtime code to deeply immutable snapshots with `new` stripped (`E0520` on `let mut`; use `clone(...)` for a mutable copy). First-class runtime references to a `meta fn` fail `E0810`.
  - `typeof expr` checks `expr` in an isolated shadow scope without evaluating it or running compile-time `meta fn` evaluation (carrying the baseline schema without `new` or source authority).
    - Internal `E0549` and statement `E0720` apply (root `Result` is exempt from `E0720`); outward `@Eff`, `&State`, `E0527` uses, and caller `E0549` endings are empty.

```ril
meta fn build_lookup(scale: int) -> []int {
    [1 * scale, 2 * scale, 3 * scale]
}
-- meta let BAD_FN = \x: int -> x      -- Error [E0816]: callable cannot escape 'meta let'

fn sample(i: int) -> int {
    let table = build_lookup(10)       -- OK: compile-time evaluated immutable []int snapshot
    -- let mut bad = build_lookup(10)  -- Error [E0520]: compile-time 'meta fn' strips 'new' qualification
    -- let fn_ref = build_lookup       -- Error [E0810]: 'meta fn' is not a runtime function value
    table[i]
}
type SampleOut = typeof(sample(0))     -- int (unevaluated)
-- fn ghost(mut xs: []int) -> int { let _: typeof({ Array::push(mut xs, 1); 0 }) = 0; len(ref xs) } -- Error [E0527]
assert(sample(1) == 20 && <SampleOut> == <int>)
```

### Semantic Interfaces and Diagnostic Boundaries

- **K-IFACE**: Module semantic interfaces retain normalized parameter/return schemas, labels and defaults, `via` mode correlations, `use` cleanup declarations, `Sendable`/`SharedObject` facts across `opaque` boundaries, effect sets, and minimal provenance relations across compilation-unit boundaries.
  - Return and storage metadata maps `new`/existing subgraphs and concrete effects/state of open `@`/`&`/`@&` callables to nested member/element paths and branch alternatives, preserved across generic substitution, aliases, record/collection storage, and module export.

---

## Declarations and Bindings

### Binding Modes and Storage Matrix

| Form | Slot rebinding | Interior access | Required source |
| :--- | :---: | :--- | :--- |
| `let x = e` | Fixed (`E0501`) | Deeply immutable (`E0520`) | Snapshot free of live writers/refs (`E0535`) |
| `var x = e` | Reassignable | Deeply immutable (`E0520`) | Snapshot free of live writers/refs (`E0535`) |
| `let mut x = e` | Pinned (`E0502`) | Writable; existing root sharing requires acknowledgment | `new`-qualified / constructor or unshared writable source; contained shared sources remain shared |
| `var mut x = e` | Reassignable | Writable; existing root sharing requires acknowledgment | Non-foreign `new`-qualified / constructor (`E0532` on `.d.ril` handles; cannot anchor `let ref`, `E0531`) |
| `let ^mut x = e` | Pinned (`E0502`) | Shared writable | Existing writable binding (bare or `^mut` result) or `new` `&up` closure retaining a `^mut`/shared local source |
| `var ^mut x = e` | Reassignable | Shared writable | Writable binding (bare on init; `^mut` marker on replacement). A fresh initial object requires later shared reception. |
| `let ref x = e` | Pinned (`E0502`) | Read-only live view (`E0520`) | Pinned `let mut`, non-`var` `ref` view, immutable shared object, or `new`-qualified composite / `&up(ref)` closure carrying live `ref` sources (`E0531` on `var` / `var ref`, `E0543` on pure/immutable temporary) |
| `var ref x = e` | Reassignable | Read-only live view (`E0520`) | Eligible source whose scope encloses `x` (`ref expr` or `ref` view on replacement; `E0357`, `E0531`, `E0543`, `E0604`) |
| `use [mut] x = e` | Pinned & confined (`E0502`, `E0604`) | `ref` (`use x`) or `mut` (`use mut x`) | Satisfies $\max(M_{\text{body}}, M_{\text{clean}})$ for type's `use(<fn>)` cleanup (`E0541`) |

```ebnf
LetDecl               ::= [ Visibility ] "let" UnmodifiedPattern [ ":" TypeExpression ] "=" Expression
LetMutDecl            ::= "let" "mut" UnmodifiedPattern [ ":" TypeExpression ] "=" Expression
SharedMutDecl         ::= "let" "^mut" UnmodifiedPattern [ ":" TypeExpression ] "=" Expression
                        | "var" "^mut" ( ValueName | Wildcard ) [ ":" TypeExpression ] "=" Expression
VarDecl               ::= "var" ( ValueName | Wildcard ) [ ":" TypeExpression ] "=" Expression
VarMutDecl            ::= "var" "mut" ( ValueName | Wildcard ) [ ":" TypeExpression ] "=" Expression
LetRefDecl            ::= "let" "ref" UnmodifiedPattern [ ":" TypeExpression ] "=" Expression
VarRefDecl            ::= "var" "ref" ( ValueName | Wildcard ) [ ":" TypeExpression ] "=" Expression
ModePreservingBinding ::= "let" "via" UnmodifiedPattern [ ":" TypeExpression ] "=" Expression
UseResourceDecl       ::= "use" [ "mut" ] ( ValueName | Wildcard ) [ ":" TypeExpression ] "=" Expression
```

#### Reachable Authority Use

Every declared mutable slot, writable binding, shared-authority marker, and mutable parameter must have a statically reachable use after literal dead-branch pruning (`E0527: UnusedAuthorityError`).
- Code after `never` transfers, literal `if false` / `while false`, `typeof(...)`, signature guards, and circular recursive self-forwarding do not count; `meta let` platform branches remain checked.

| Declared authority | Required reachable use (`E0527` when absent) |
| :--- | :--- |
| `var x` / `var ref x` | Reachable slot replacement (`x = ...` or compound assignment) |
| `let mut x` / `mut p` parameter | Reachable interior write, `mut`/`^mut` forwarding to a non-circular writer, or `new` handoff |
| `use mut x` | Reachable interior write or `mut` argument forwarding inside the block (`use mut _` always fails `E0527`; write `use x` or `use _`) |
| `var mut x` | Both reachable slot replacement and reachable writable or `new`-handoff use |
| `let ^mut x` | Both shared writable reception and reachable writable use |
| `var ^mut x` | Reachable slot replacement, shared writable reception, and reachable writable use |
| `^mut p` parameter / handler binder | Surviving writable retention beyond call/arm scope (root `-> ^mut(p)`, `&return(^mut p)`, `&^mut` store, or `&capture`; mutating `p` alone without retention fails `E0527`) |
| `^mut expr` sharing marker | Target requires shared writable authority (`let ref r = ^mut src` fails `E0527`) |
| Contextual callback `_` / `_name` | Named `fn` and standalone closures enforce `E0527` on `_`/`_name`; an `AnonFnExpr` checked directly against an expected `CallableType` (`derive \mut _d -> ()`, `run_hook(mut c) \mut _ -> ()`, `with Eff::op = \mut _ -> ...`) exempts `_`/`_name` |

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
-- fn loop_mut(mut x: Cell) -> () { loop_mut(mut x) }     -- Error [E0527]: circular recursive forwarding
-- let ^mut unshared = Cell.{ count: 0 }; unshared.count += 1 -- Error [E0527]: unshared root needs 'let mut', not '^mut'
-- let ref bad_mark = ^mut c                   -- Error [E0527]: redundant '^mut' marker for 'ref' target
```

### New-Qualified Locals and Mode-Preserving Reception

A pinned `let mut` (fixed binding slot, independent of physical object relocation) initialized by construction, `clone`, or a `new`-qualified result retains `new` qualification while its `new` subgraphs have no independent surviving outside aliases.

Contained existing sources keep their own provenance; `new x` preserves identity, ends `x` and dependent paths (`E0549`), and leaves independent existing-source paths valid. Handing off or freezing a `new`-qualified local always requires explicit `new x`—including at return boundaries (`new b`, `Ok(new out)`), never implicitly transferring on scope exit. On a named `fn`, returning a `new`-qualified `SharedObject` requires declaring `-> new T` (`E0544`); whether to freeze or mutate it is decided by the caller.

Receiving an existing writer in a persistent `let mut` or `var mut` binding requires an explicit `new` handoff (`E0510`). A `mut` parameter can yield another call-scoped `mut` borrow. Creating shared writable storage from that borrow fails with `E0528`. An existing `^mut` member keeps its shared authority when reached through a `mut` parameter.

A `var ^mut` slot initialized with a fresh object must receive an existing writer in a reachable replacement (`E0527`). Applying `^mut` to a fresh object sets its mode and leaves the requirement for shared reception outstanding.

```ril
type Buffer = .{ mut items: []int }

fn build_buffer() -> new Buffer {
    let mut b = Buffer.{ items: [] }
    b.items |> mut Array::push(1)
    new b                              -- OK: explicit 'new' handoff; local write stays local
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

### Immutable, Mutable, Shared, and Read-Only View Bindings

```ril
-- 1. Pinned immutable, writable ('mut'), shared ('^mut'), and live read-only ('ref') bindings:
type Doc = .{ var title: str }
let fixed_doc  = Doc.{ title: "v0" }
let mut draft  = Doc.{ title: "v1" }
let ^mut shared = draft                -- Explicit shared writable binding
let ref reader  = draft                -- Pinned read-only live view

shared.title = "v2"
draft.title  = "v3"
assert(reader.title == "v3")

-- Rejected on pinned bindings:
-- fixed_doc = Doc.{ title: "v1" }     -- Error [E0501]: plain 'let' slot cannot be reassigned
-- let mut bad_unack = draft           -- Error [E0510]: shared alias requires '^mut' acknowledgment
-- reader.title = "v4"                 -- Error [E0520]: 'ref' grants no write authority
-- draft = Doc.{ title: "new" }        -- Error [E0502]: 'let mut' binding is pinned
-- let ref bad_temp = Doc.{ title: "x" } -- Error [E0543]: unanchored temporary cannot bind 'let ref'
```

```ril
-- 2. Reassignable 'var' and 'var ref' slots:
type Doc = .{ var title: str }
let fixed_doc = Doc.{ title: "v0" }
let mut draft = Doc.{ title: "v1" }
draft.title = "v2"
var slot = Doc.{ title: "snap1" }
slot = Doc.{ title: "snap2" }          -- OK: slot replacement of immutable snapshots
-- let ref bad_obs = slot              -- Error [E0531]: reassignable 'var' cannot anchor 'let ref'

var ref cur_view = fixed_doc
cur_view = ref draft                   -- OK: 'var ref' reassignment takes explicit 'ref'
-- cur_view = fixed_doc                -- Error [E0357]: 'var ref' slot requires 'ref' expression
-- let ref bad_vref = cur_view         -- Error [E0531]: reassignable 'var ref' cannot anchor 'let ref'
```

```ril
-- 3. Collection element modes match strictly:
type Doc = .{ var title: str }
let fixed_doc = Doc.{ title: "v0" }
let mut docs: []Doc = [fixed_doc]      -- Plain immutable elements
Array::push(mut docs, fixed_doc)
let mut views = [ref fixed_doc]        -- Explicit 'ref' synthesizes '[ref]Doc'
Array::push(mut views, ref fixed_doc)

-- Rejected on collection elements:
-- let mut bad_views: [ref]Doc = [fixed_doc] -- Error [E0357]: plain element != '[ref]Doc'
-- Array::push(mut views, reader)      -- Error [E0531]: mutable collection 'ref' slot rejects local live 'ref' view
```

### Scoped Resource Bindings

`use [mut] x = expr` anchors a non-escaping resource in a block slot for the remainder of the enclosing block whose static type `T` declares an accessible `use(<fn_name>)` cleanup declaration (`E0541` otherwise).

```ril
pub opaque type DbConn use(close) = .{ var open: bool, mut log: []str }

pub fn close(new c: DbConn) @io -> () {
    let mut conn = new c
    conn.open = false
    println("closed")
}
pub fn acquire() -> new DbConn { DbConn.{ open: true, log: [] } }

fn run_query() @io -> new !<int, str> {
    use ro = acquire()                 -- Exposes 'ref' in body; runs close(new ro) on exit
    assert(ro.open)
    use mut conn = acquire()           -- Exposes 'mut' in body; requires body write
    conn.log |> mut Array::push("SELECT 1")
    Ok(1)                              -- LIFO cleanup: close(new conn), then close(new ro)
}
```

```ril
-- Rejected scoped resource cases:
-- close(new conn)                     -- Error [E0604]: scoped source path cannot end early
-- use mut idle = acquire()            -- Error [E0527]: 'use mut' has no body write; write 'use'
-- use bad_plain = 42                  -- Error [E0541]: 'int' has no 'use' cleanup declaration
-- use var bad = acquire()             -- Error [E0532]: 'use' bindings forbid 'var'
-- return conn                         -- Error [E0604]: 'use' binding cannot escape block
-- pub opaque type BadFiber use(fiber_close) = .{ fd: int }
-- pub fn fiber_close(new _c: BadFiber) @fiber -> () {} -- Error [E0616]: '@fiber' prohibited on cleanup
-- fn missing_io() -> () { use _ = acquire() }          -- Error [E0612]: unhandled @io from close
```

- **Eligible declarations (`E0541`)**: `use(fn_name)` is valid on `SharedObject` `OpaqueTypeDecl` / `NominalTypeDecl` / `SumTypeDecl` and `.d.ril` equivalents (`E0541` on aliases or value types).
  - `fn_name` must resolve in the same scope to `fn(ref Self) [@Eff] -> ()`, `fn(mut Self) [@Eff] &mut -> ()`, or `fn(new Self) [@Eff] -> ()` without `&^mut` or `&capture`, satisfying `E0910`.
- **Body mode & reception**: `use x` exposes `ref` (`use _` keeps an anonymous slot); `use mut x` exposes `mut` (`E0527` requires a body write). `expr` is checked against $\max(M_{\text{body}}, M_{\text{clean}})$ under $\text{\texttt{ref}} < \text{\texttt{mut}} < \text{\texttt{new}}$ (`E0548`, `E0520`).
- **Cleanup effects (`E0616`, `E0612`)**: Synchronous `@io` and user `fn` effects are allowed and charged at the `use` site (`E0612`); `@fiber` is prohibited (`E0616`). `with` handlers declared **above** `use` handle its cleanup `@Eff`; handlers declared **below** exit earlier and do not.
- **Confinement (`E0532`, `E0604`)**: Forbids `use var` (`E0532`), `^mut` sharing, rebinding, early `new x` handoff, return escape, and closure/fiber capture (`E0604`, `E0601`).
- **LIFO execution**: Cleanup runs once per initialized binding in reverse order on normal exit, `return`, `break`, `continue`, `?`, panic unwinding, and unshielded `@fiber` cancellation; a panic inside cleanup during active unwinding triggers immediate uncatchable program termination (abort).

### Declaration Metadata Attributes

Compile-time `meta(expr1, expr2)` attributes attach deeply immutable constant values (`E0814` on non-static expressions; `E0812`/`E0816` on type values or callables).
- Permitted on `nominal type`, `opaque type`, sum, `sub`, nominal/opaque root record fields, variants, effects, and functions (`E0708` on transparent aliases, structural record fields, `use` imports/bindings, or local `let`/`var`).

```ril
pub nominal type Route = str
pub nominal type Role  = str

meta(Route("/users"), Role("admin"))
pub nominal type CreateUserReq = .{
    meta(Role("pii"))
    email: str,
}
-- meta(Route("/x")) type BadAlias = int              -- Error [E0708]: 'meta(...)' prohibited on transparent alias
-- type BadFieldMeta = .{ meta(Role("pii")) id: int } -- Error [E0708]: structural record field forbids 'meta(...)'
```

```ebnf
MetaAttr    ::= "meta" "(" MetaArgList ")"
MetaArgList ::= Expression { "," Expression } [ "," ]
```

### Foreign Interface Declarations

Foreign interface declarations reside in bodyless `.d.ril` files (`DeclFile`).

```ril
-- File: sys/posix.d.ril
pub opaque type HostFd use(close)

pub fn open_path(path: str) @io -> new !<HostFd, str>
pub fn read_bytes(ref fd: HostFd, max_len: int) @io -> new !<bytes, str>
pub fn close(new fd: HostFd) @io -> ()
pub sub Signals {
    pub let sigint: int
}
```

```ril
-- Rejected foreign interface and usage cases:
-- pub fn bad_body() -> int { 1 }          -- Error [E0901]: bodies prohibited in .d.ril
-- pub fn bad_shared(^mut fd: HostFd) -> () -- Error [E0908]: '^mut' unsupported on foreign signatures
-- pub fn bad_snap(fd: HostFd) -> ()       -- Error [E0908]: foreign opaque handle requires ref/mut/new
-- In .ril file:
-- fn unimplemented() -> int               -- Error [E0902]: body required in standard .ril module
-- let _ = fd.internal_handle              -- Error [E0907]: foreign representation is sealed
```

- **Bodyless `.d.ril` (`E0901`, `E0902`)**: `.d.ril` forbids function bodies, initializers, field defaults, `=` bodies on `opaque type`, and `opaque` on sum/nominal/alias declarations (`E0901`). Bodyless functions or `opaque type` in `.ril` fail `E0902` unless matching a registered built-in.
- **Sealing & signatures (`E0907`, `E0908`, `E0906`)**:
  - Foreign `opaque type` and `nominal type` shapes cannot be constructed, unwrapped via `inner`, or accessed via fields, patterns, or introspection in `.ril` (`E0907`, taking precedence over `E0308`).
  - Foreign signatures forbid `^mut`, `&^mut`, `&capture`, `via`/`infer`, and unannotated plain `DeclOpaqueType` parameters/returns (`E0908`).
  - `DeclLet` admits pure immutable data constants only (`E0906`); host-stateful foreign functions must declare `@io` for `absorb_panic` isolation (`E0608`).
- **Foreign `opaque type` handle matrix** (e.g., `pub opaque type HostFd use(close)`):

| Allowed | Forbidden |
| :--- | :--- |
| `new` creation and single-use `new fd` handoff (`E0549` after handoff) | `clone` (`E0301`), `derive` (`E0536`), `==` (`E0327`) |
| `let mut`, call-scoped `mut`, `ref` view, and scoped `use` | Plain `let`/`var` freezing (`E0535`), `var mut` overwrite (`E0532`), `^mut` (`E0908`/`E0510`) |
| *(exclusive, non-duplicable host handle)* | `[M]HostFd`, `[K: M HostFd]`, `Set<HostFd>` storage (`E0301`, `E0328`) |

```ebnf
DeclUnitItem    ::= UseDecl | DeclSub | DeclFunction | DeclType | DeclEffect | DeclLet
DeclSub         ::= { MetaAttr } [ Visibility ] "sub" PascalCase
                    "{" { DeclUnitItem Separator } [ DeclUnitItem ] "}"
DeclFunction    ::= { MetaAttr } [ Visibility ] "fn" ValueName [ GenericParams ]
                    "(" [ ParameterList ] ")" ReturnSpec
DeclType        ::= DeclSumType | DeclNominalType | DeclTypeAlias | DeclOpaqueType
DeclTypeHead    ::= { MetaAttr } [ Visibility ] "type" PascalCase [ GenericParams ]
DeclNominalHead ::= { MetaAttr } [ Visibility ] "nominal" "type" PascalCase [ GenericParams ]
DeclSumType     ::= DeclTypeHead [ UseCleanupClause ] "{" [ VariantDeclList ] "}"
DeclNominalType ::= DeclNominalHead [ UseCleanupClause ]
DeclTypeAlias   ::= DeclTypeHead "=" TypeExpression
DeclOpaqueType  ::= { MetaAttr } [ Visibility ] "opaque" "type" PascalCase [ GenericParams ]
                    [ UseCleanupClause ]
DeclEffect      ::= { MetaAttr } [ Visibility ] "eff" PascalCase [ GenericParams ]
                    "{" [ EffectMemberList ] "}"
DeclLet         ::= [ Visibility ] "let" ValueName ":" TypeExpression
```

---

## Expressions and Operators

### Expression Grammar and Precedence

| Precedence (high → low) | Operators / forms | Associativity |
| :---: | :--- | :---: |
| 1 | `.` `?.` `f(...)` `Tag(...)` `f \...` `a[i]` `a?[i]` `?` `Type.{...}` `::` | Left |
| 2 | Unary `-` `!` `~` `ref e` `^mut e` `new x` | Right |
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
| 15 | `=` `+=` `-=` `*=` `/=` `%=` `&=` `\|=` `^=` `<<=` `>>=` | Non-associative (`E0701`) |

*(Note: `let ... else` is a `Statement` form, and `where` (`BlockWhereClause`) is a trailing `Block` clause rather than an expression operator.)*

- **Lexical Adjacency (`E0338`)**: Function and constructor calls attach `(` (`parse(s)`, `Ok(42)`, `Ok()`, `Rect(10.0, 20.0)`), array/map indexing attaches `[` (`xs[0]`), and named record constructions attach `.{` (`User.{ id: 1 }`).
- **Call-Site Argument Markers (`E0406`, `E0338`)**: At the top level of a call `Argument`, leading `mut`, `ref`, `^mut`, or `new` always parses as `ArgumentMode` (`E0406` if mismatched against a plain parameter or constructor payload). Calling a unit variant, unit nominal, or concrete record type with `(...)` fails `E0338`.
- **Expression Holes (`...`, `E0360`)**: `...` has type `never`, satisfies any expected type and access mode during partial checking, and suppresses cascading `E0527` / `E0549` diagnostics along paths ending in `...`, while failing complete builds with `E0360: UnfinishedExpressionHoleError`.

```ril
type Buf = .{ var len: int }
-- fn draft_fill(mut buf: Buf) &mut -> int {
--     ...                                -- Error [E0360]: unfinished expression hole in complete build
-- }
```

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
                           | NewHandoffExpr
                           | ObserveExpr
                           | SharingExpr
                           | PostfixExpr
NewHandoffExpr           ::= "new" ValueName
ObserveExpr              ::= "ref" PostfixExpr
SharingExpr              ::= "^mut" PostfixExpr
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

### Arithmetic, Bitwise, Relational, and Logical Operators

Ril operators are strictly typed with no implicit numeric or string coercions:

```ril
assert(7 / 3 == 2 && -7 / 3 == -2 && -7 % 3 == -1)
assert((~0 == -1) && ((-8 >> 2) == -2) && ((1 << 100) > 0))
```

```ril
-- Rejected operator uses:
-- let bad_str_add = "a" + "b"          -- Error [E0327]: '+' is numeric only; write '"{a}{b}"'
-- let bad_div = 10 / 0                 -- Error [E0361]: constant zero divisor
-- let bad_shl = 1 << -3                -- Error [E0361]: constant negative shift count
-- let bad_bit = true & false           -- Error [E0327]: bitwise '&' requires 'int'
```

- **Arithmetic (`+`, `-`, `*`, `/`, `%`, unary `-`)**:
  - Defined exclusively on `(int, int) -> int` and `(f64, f64) -> f64` (`E0327` on `str`, `bytes`, or `bool`; strings combine via interpolation `"{a}{b}"`).
  - Integer `/` truncates toward zero and `%` satisfies `(a / b) * b + (a % b) == a`.
  - Syntactic literal `0` divisors fail `E0361` at check time; non-literal `/ 0` or `% 0` panics (`E0831` in static evaluation; `Numeric::checked_div` / `Numeric::checked_rem` return `?int`).
  - Explicit numeric conversions use `Numeric::to_f64(n: int) -> f64`, `Numeric::convert<int>(x: f64) -> new ?int` (exact integral conversion; `None` if fractional, NaN, or infinite), and `Numeric::trunc(x: f64) -> new ?int` (truncates finite `f64` toward zero; `None` if NaN or infinite).
- **Bitwise & Shifts (`~`, `&`, `|`, `^`, `<<`, `>>`)**:
  - Defined exclusively on `int` (`E0327` elsewhere) with infinite-width two's-complement semantics (`~x == -x - 1`, `x >> k` arithmetic floor shift).
  - Syntactic negative literal shift counts (`-k`) fail `E0361`; non-literal `k < 0` panics (`E0831` in static evaluation).
- **Equality & Ordering (`==`, `!=`, `<`, `<=`, `>`, `>=`)**:
  - `==` / `!=` require same-type operands (`E0301`, `E0305` on distinct nominals) recursively excluding callables, `.d.ril` `opaque` handles, `Scope`, `Task`, `Sender`, `Receiver`, and `Draft` (`E0327`). Structural equality over cyclic shared-object graphs is defined coinductively (greatest fixed point of componentwise equivalence) and must terminate.
  - `f64` follows IEEE-754 (`NaN != NaN`, `-0.0 == 0.0`); `?T == None` / `!= None` tests the option tag even when `T` lacks equality.
  - Map keys and `Set` elements additionally forbid `f64`, extensible `{ .. }` sums, and mutable member modes (`E0328`).
  - Static type-value exception: `Type<A>` and `Type<B>` may represent different types; `<A> == <B>` holds iff `A` and `B` are type-equivalent (`!=` is its complement), regardless of value equality.
  - `<`, `<=`, `>`, `>=` apply to same-type `int`, `f64`, `str` (lexicographic UTF-8 scalar order), and `bytes` (`E0327` elsewhere).
- **Logical (`!`, `&&`, `||`)**: Require `bool` operands (`E0350`); `&&` and `||` short-circuit left-to-right.

### Indexing, Slicing, and Static Coordinate Projection

```ril
let xs = [10, 20, 30, 40]
let text = "hello, 世界"
assert(xs[1..3] == [20, 30] && xs?[9] == None && text[0..5] == "hello")
let m = ["port": 8080]
assert(m?["port"] == Some(8080) && m?["host"] == None)

type Cell = .{ var v: int }
let mut cells = [Cell.{ v: 1 }]
let ref elem = cells[0]
assert(elem.v == 1)
cells |> mut Array::push(Cell.{ v: 2 }) -- OK: 'elem' last use has ended
```

```ril
-- Rejected indexing & live-hold overlaps:
-- let _ = m["port"]                    -- Error [E0352]: map read requires 'm?["port"]'
-- let _ = "abc"[0]                     -- Error [E0352]: 'str' element access uses 'String::at'
-- let _ = Some(1).0                    -- Error [E0337]: sum has no '.0' projection
-- let ref elem = cells[0]; cells |> mut Array::push(Cell.{ v: 2 }); assert(elem.v == 1) -- Error [E0537]
```

- **Arrays `[M]T`**: Accept `int` element indices (`xs[i]` panics out of bounds; `xs?[i] -> ?T` returns `None`). Single-element bracket indexing on `str` or `bytes` fails `E0352` (use `String::at` / `Bytes::at`); dynamic bracket indexing on records fails `E0324`.
- **Slicing (`s[a..b]`, `s[a..=b]`, `s?[a..b]`)**: Produces a fresh `new`-qualified array on `[M]T` (preserving element modes; binding directly to `let ref` fails `E0543`), a Unicode-scalar sub-string on `str`, and a byte sub-sequence on `bytes`.
- **Maps `[K: M V]`**: Reads require safe lookup `m?[k] -> ?V` (`E0352` on `m[k]` reads or `m[k] += v`); direct slot assignment `m[k] = v` inserts or updates key `k`.
- **Container Element Holds (`E0537`, `E0526`)**: On live `[M]T` and `[K: M V]` containers, `xs[i]`, `xs?[i]`, and `m?[k]` establish scoped element holds bounded by the container; mutating or resizing the container while a `ref`/`mut` hold is active or during `for` iteration fails `E0537` / `E0526`.
- **Tuple & Static Coordinate Projection (`t.0`, `r.(key)`)**: `t.0` projects tuple elements (`E0312` out of bounds; `E0337` on sums, records, collections, or primitives). `r.(key)` projects an accessible record field or tuple slot using a compile-time `meta` coordinate validated by `Key<T>`.

### Text and Byte Operations

Strings combine via interpolation `"{left}{right}"` or `String::join`. Prelude modules `String` and `Bytes` provide dual-phase text, diagnostic formatting, and byte operations:

```ril
type Pair = .{ var id: int, label: str }
let mut p = Pair.{ id: 6, label: "ok" }
p.id = 7
assert(String::inspect(ref p) == #".{ id: 7, label: "ok" }"# && String::inspect(Some(3)) == "Some(3)")
assert(String::starts_with("src/lexer.ril", "src/") && String::ends_with("src/lexer.ril", ".ril"))
assert(Bytes::from_array([65, 66]) == Some(bytes"AB") && Bytes::from_array([256]) == None)
assert(String::decode_utf8(String::encode_utf8("Ril")) == Some("Ril"))
assert(String::decode_utf8(bytes"\xC0\xAF") == None)
```

- **`String::inspect<T>(via value: T) -> str`**: Pure dual-phase diagnostic formatter accepting plain values/snapshots or `ref` shared-object views (`E0401` on `ref` value types; `mut`/`^mut`/`new` markers rejected).
  - Formats primitives, escaped `str`/`bytes` literals, tuples, collections, and transparent records/nominals/sums structurally (rendering runtime reference cycles as `"..."`).
  - Formats sealed `opaque` types outside their defining scope, `.d.ril` `opaque` handles, callables, and runtime concurrency/draft handles as `"<TypeName>"` (or `"<fn>"`).
- **String helpers**: `String::join(via parts: []str, separator: str) -> str` joins parts in array order and returns an empty string for an empty array. `String::starts_with(text: str, prefix: str) -> bool`, `String::ends_with(text: str, suffix: str) -> bool`, `String::at(text: str, index: int) -> new ?int`, `String::scalars(text: str) -> new []int`, `String::from_scalars(via values: []int) -> new ?str`.
- **UTF-8 & Bytes helpers**: `String::encode_utf8(text: str) -> bytes`, `String::decode_utf8(data: bytes) -> new ?str` (`None` on ill-formed UTF-8), `Bytes::at(data: bytes, index: int) -> new ?int`, `Bytes::to_array(data: bytes) -> new []int`, `Bytes::from_array(via values: []int) -> new ?bytes` (`None` outside `0..=255`).

### Pipeline and Fallible Operators

```ril
type Config = .{ host: ?str }
type Route  = .{ pair: (str, int) }
fn resolve_host(cfg: ?Config) -> str { cfg?.host ?? "localhost" }
fn parse_pos(s: str) -> new !<int, str> { if s == "80" { Ok(80) } else { Err("bad") } }
fn check_port(p: int) -> new !<int, str> { if p > 0 { Ok(p) } else { Err("zero") } }
fn load_port(raw: str) -> new !<int, str> { Ok(raw |> parse_pos? |> check_port?) }

let maybe_r: ?Route = Some(Route.{ pair: ("db", 5432) })
assert(maybe_r?.pair.1 == Some(5432) && [10, 20]?[1] == Some(20))

let mut buf = [1, 2]
buf |> mut Array::push(3)
assert(buf |> ref len == 3 && resolve_host(None) == "localhost")
assert(load_port("80") == Ok(80) && load_port("x") == Err("bad"))
```

```ril
-- Rejected pipeline, propagation, fallback, and safe-navigation forms:
-- let _ = (maybe_r?.pair).1            -- Error [E0337]: parentheses end '?.' chain, yielding '?(str, int)'
-- clone(ref buf) |> mut Array::push(4) -- Error [E0410]: '|> mut' requires an addressable writable path
-- let top_q = Ok(1)?                   -- Error [E0205]: '?' outside function/closure frame
-- let _ = 1 |> 2                       -- Error [E0338]: pipeline target is not callable
-- let _ = 42?                          -- Error [E0712]: '?' requires Result or Option
-- fn bad_prop() -> int { None? }       -- Error [E0713]: enclosing return type is not Option
-- let _ = 42 ?? 0                      -- Error [E0714]: '??' requires Option or Result
-- let _ = Ok(1) ?? 0                   -- Error [E0711]: Result '??' requires error handler 'fn(E) -> T'
-- let _ = 42?.host                     -- Error [E0715]: '?.' requires optional '?T' receiver
-- fn bad_fb(o: ?int) -> int { o ?? return 0 } -- Error [E0710]: control transfer inside '??' fallback
```

- **Mode-Aware Pipelines (`x |> [mode] f(a) [\...] [?]`)**: Evaluates `x`, then `f` and remaining arguments left-to-right (`E0338` if `f` is non-callable), passing `x` as the first argument under `[mode]`. An optional trailing `?` propagates on that step's call result (`x |> f(a)?` ≡ `(f(x, a))?`):

| Pipeline form | Equivalent call | Left-operand requirement |
| :--- | :--- | :--- |
| `x \|> f` / `x \|> f(a)` | `f(x)` / `f(x, a)` | `Expression` (immutable snapshot, value copy, or lexical `via`) |
| `x \|> ref f` / `x \|> ref f(a)` | `f(ref x)` / `f(ref x, a)` | `Expression` (scoped read-only `ref` access) |
| `x \|> mut f` / `x \|> mut f(a)` | `f(mut x)` / `f(mut x, a)` | Addressable writable path (`E0410` on non-addressable or temporary expressions) |
| `x \|> ^mut f` / `x \|> ^mut f(a)` | `f(^mut x)` / `f(^mut x, a)` | Addressable writable path (`E0410` on non-addressable or temporary expressions) |
| `x \|> new f` / `x \|> new f(a)` | `f(new x)` / `f(new x, a)` | `Expression` (ends `x` before evaluating `f` or `a`, `E0549`) |

- **Error/Option Propagation (`expr?`)**: Valid inside ordinary functions or closures (`E0205` at module/`sub` top-level). Preserves the `Ok`/`Some` payload's own mode, `new` qualification, and contained sources (a `new` sum wrapper does not make an existing payload `new`):
  - On `!<T, E>` (`E0712` on non-`Result`/non-`Option`): unwraps `Ok(v)` to `v`, or returns `Err(e)` (widening `e` when $E \preceq_{\text{sum}} E_{\text{ret}}$; incompatible enclosing return types fail `E0713`).
  - On `?T`: unwraps `Some(v)` to `v`, or returns `None` when the enclosing callable returns `?U` (`E0713` otherwise).
- **Right-Associative Fallback (`opt ?? b ?? c` / `res ?? \err -> fallback`)**:
  - `?T ?? T`: evaluates right operand lazily only on `None` (`E0714` on invalid left operand).
  - `!<T, E> ?? fn(E) @... -> T`: invokes the handler closure with `e` on `Err(e)`, satisfying `E0720` (`E0711` if right operand is not `fn(E) -> T`; outer `break`/`continue`/`return` across a fallback or closure boundary fails `E0707`/`E0710`).
- **Safe Navigation (`opt?.field`, `opt?[idx]`)**:
  - `?.` requires `?T` (`E0715`); `?[` accepts direct or `?`-wrapped `[M]T`, `[K: M V]`, `str` (slice), and `bytes` (slice) (`E0352` / `E0715`).
  - Within an unparenthesized postfix chain, `?.` / `?[` short-circuits `None` to the end of the chain and lifts the result once to `?R` without double-wrapping.

### Record Construction and Assignments

```ril
var a = 1
var b = 2
a += b
b += 1
assert(a == 3 && b == 3)
-- 10 = 20                             -- Error [E0503]: invalid assignment target
-- a = b = 3                           -- Error [E0701]: chained assignment is prohibited
```

- **Record Construction (`[Type].{ [MemberMode] field: expr, shorthand }`)**: Must initialize every non-defaulted declared field of the target record type (`E0307` missing, `E0302` unexpected, `E0210` duplicate). Field shorthand `.{ id, name }` desugars to `.{ id: id, name: name }`. On anonymous `.{ ... }`, `[ MemberMode ]` explicitly declares the field's mode (or a `ref expr` value synthesizes a `ref` field; `var` is never synthesized implicitly, `E0357`). On named `Type.{ ... }`, fields inherit `Type`'s declared modes (any written `[ MemberMode ]` must match, `E0357`, and `ref` fields require a `ref`-mode expression).
- **Assignment Semantics (`target = expr`, `target += expr`, ...)**: Assignment is a `()`-typed expression and does not chain (`a = b = 1` fails `E0701`). Compound assignments evaluate `target`'s receiver/index expression exactly once.
- **Valid `AssignTarget`**: Must be a `var` variable, a `var` record field on a `mut`/`^mut` path, an element of a `mut`/`^mut` array/map, or a field/tuple slot on a confined `mut Draft<T>` path.
  - Fails `E0501` on `let` or plain fields, `E0502` on pinned `let mut`/`let ref`, `E0503` on temporaries or non-draft tuple slots, and `E0352` on map compound assignment `m[k] += v`.

---

## Control Flow and Pattern Matching

### Block Expressions and Local Declarations

A block evaluates its statements top-to-bottom and yields its trailing expression (or `()` if empty, terminated by `;`, or ending in a declaration/statement such as `let`, `var`, `use`, `with`, or `let ... else`). Local `fn`, `meta fn`, `type`, and `eff` declarations are hoisted into a trailing `where` clause:

```ril
fn compute_tree() -> int {
    let base = 10
    sum(Node(Leaf(1), Leaf(2)))         -- Returning 'Leaf(1)' from 'compute_tree' would fail E0315
where
    type Tree { Leaf(int); Node(Tree, Tree) }
    fn sum(t: Tree) &up(base) -> int {
        match t {
            Leaf(v)    -> v + base
            Node(l, r) -> sum(l) + sum(r)
        }
    }
}
assert(compute_tree() == 23)
```

```ril
-- Rejected block declaration and initialization orders:
-- let bad_self = bad_self + 1         -- Error [E0207]: 'bad_self' used before initialization
-- fn seq_fn() -> int { 1 }            -- Error [E0703]: move local 'fn' to trailing 'where' clause
-- let early = sum(Leaf(1))            -- Error [E0207]: 'sum' captures 'base' before 'base' is initialized
-- where let bad_where_let = 1         -- Error [E0702]: value bindings are prohibited in 'where'
-- where eff EscEff { fn ping() -> () } -- Unhandled EscEff::ping() in block fails E0618
```

- **Hoisted `BlockWhereClause` (`E0702`, `E0703`)**: Local `fn`, `meta fn`, `type`, and `eff` declarations belong in the block's trailing `where` clause (`E0703` if placed in `StatementSequence`); value bindings (`let`, `var`), `sub`, or statements inside `BlockWhereClause` fail `E0702`.
- **Initialization Order (`E0207`)**: All `BlockWhereClause` items form one mutually recursive scope hoisted across the block. Value bindings (`let`, `var`, `use`) enter scope strictly after their initializer completes; calling a `where` helper before an outer local it captures is initialized fails `E0207`.
- **Local Type Confinement (`E0315`)**: Local nominal, `opaque`, and sum types declared in `SignatureWhereClause` or `BlockWhereClause` cannot escape in the enclosing signature or outer mutable storage (transparent `type` aliases in `SignatureWhereClause` expand cleanly).
- **Local Effects & Visibility (`E0618`, `E0703`, `E0120`)**: Block-local `eff` effects must be handled inside their declaring block (`E0618`), and visibility modifiers (`pub`, `pkg`) are prohibited (`E0703` / `E0120`).

```ebnf
Block             ::= "{" [ StatementSequence ] [ BlockWhereClause ] "}"
StatementSequence ::= Statement { Separator Statement } [ Separator ]
Statement         ::= UseDecl
                    | MetaLetDecl
                    | LetDecl | LetMutDecl | SharedMutDecl
                    | VarDecl | VarMutDecl | LetRefDecl | VarRefDecl
                    | ModePreservingBinding | UseResourceDecl
                    | LetElseStmt
                    | WithStatement
                    | ControlTransfer
                    | Expression
BlockWhereClause  ::= "where" BlockWhereItem { Separator BlockWhereItem } [ Separator ]
BlockWhereItem    ::= FunctionDecl | LocalTypeDecl | EffectDecl | MetaFnDecl
Separator         ::= ";" | Newline
```

### Conditional and Loop Expressions

```ril
fn find_odd_sum() -> int {
    var acc = 0
    for 1..=10 as i {
        if i % 2 == 0 { continue }
        if i > 7 { break }
        acc += i
    }
    while true {
        return acc                         -- 'while true' with no targeting 'break' has type 'never'
    }
}
assert(find_odd_sum() == 16)
```

```ril
-- Rejected control-flow forms:
-- if 1 { () }                         -- Error [E0350]: condition must be 'bool'
-- let _ = if true { 1 } else { "no" } -- Error [E0351]: incompatible branch types 'int' and 'str'
-- for 42 as x { () }                  -- Error [E0355]: 'int' is not iterable
-- break                               -- Error [E0707]: 'break' outside loop
```

- **Conditionals (`E0350`, `E0351`)**: `if cond { a } else { b }` requires `cond: bool` (`E0350`) and a common join type across normal branches (`E0351`). Without `else`, the `then` block must have type `()` or `never`. `if let [mode] pat = expr` matches a partial pattern.
- **`while` & `while true` (`E0350`)**: `while cond { body }` (`cond: bool`) and `while let [mode] pat = expr { body }` check `body` against `()`. A bare `while true { ... }` with no `break` targeting that loop (ignoring `break`s inside nested loops) has type `never`; all other `while` loops have type `()`.
- **`for` Loops (`E0355`, `E0345`, `E0526`)**: `for [mode] iter as pat { body }` iterates over `[]T`, `[K: V]` (yielding `(K, V)`), `Set<T>`, or integer ranges `a..b` / `a..=b` (`E0355` otherwise), checks `body` against `()`, and requires an always-matching `pat` (`E0345`).
  - Plain `for` / `for ref` holds a static read hold on live collections; `for mut` / `for ^mut` exposes element writes while forbidding structural resize/reallocation (`E0526`); `for new` hands off a `new` collection and yields `new` elements; `for via` preserves a `via`-dependent collection's instantiated mode.
- **Control Transfers (`E0707`)**: `break` and `continue` target the innermost enclosing `while` or `for` in the same callable (`E0707` outside a loop or across a closure boundary). `return` exits the innermost enclosing `fn` or `\... ->` closure (`return` ≡ `return ()`).

```ebnf
IfExpr          ::= "if" ( Expression | "let" [ "mut" | "ref" | "^mut" | "via" ] UnmodifiedPattern "=" Expression ) Block
                    [ "else" ( IfExpr | Block ) ]
WhileExpr       ::= "while" ( Expression | "let" [ "mut" | "ref" | "^mut" | "via" ] UnmodifiedPattern "=" Expression ) Block
ForExpr         ::= "for" [ "ref" | "mut" | "^mut" | "new" | "via" ] ForIterable "as" Pattern Block
ControlTransfer ::= "return" [ Expression ]
                  | "break"
                  | "continue"
```

### Let-Else Bindings

`let Pat = expr else { ... }` unpacks a partial pattern on the happy path and requires the `else` block to diverge (`never`):

```ril
fn validate(header: ?str, check: fn(str) -> !<(), str>) -> new !<str, str> {
    let Some(str["Bearer ", ..token]) = header else { return Err("missing bearer") }
    let Ok() = check(token) else { return Err("invalid token") }
    Ok(token)
}
```

```ril
-- Rejected let / let-else patterns:
-- let Some(x) = header             -- Error [E0345]: partial pattern in 'let' without 'else'
-- let () = ()                      -- Error [E0309]: zero-binding pattern binds no names
-- let Some(y) = header else { () } -- Error [E0321]: 'else' block must diverge ('never')
```

- **Diverging `else` (`E0321`)**: On pattern mismatch, `else` must diverge (`never` via `return`, `break`, `continue`, `panic`, or `?`; normal completion fails `E0321`). `let ... else` is exempt from `E0309`, allowing zero-binding assertions such as `let Ok() = check() else { ... }`.
- **Plain `let` (`E0345`, `E0309`)**: `let Pat = expr` without `else` requires an always-matching pattern (`E0345`) that binds at least one name (except explicit `let _ = expr`; `let () = f()` or `let Marker = m` fails `E0309`).

```ebnf
LetElseStmt ::= "let" [ "mut" | "ref" | "^mut" | "via" ] UnmodifiedPattern "=" Expression "else" Block
```

### Pattern Matching

Patterns mirror Ril's construction syntax across records, tuples, sum variants, arrays, integer ranges, and non-overlapping `str[...]` slices:

```ril
fn classify_packet(raw: str) -> str {
    match raw {
        str["{{", ..body, "}}"] -> "json:{body}" -- Requires len(raw) >= 2; "{" does NOT match!
        str["GET ", ..path]     -> "get:{path}"
        _                       -> "other"
    }
}
assert(classify_packet(#"{ok}"#) == "json:ok" && classify_packet(#"{"#) == "other")
```

```ril
-- Rejected pattern and match forms:
-- match true { true -> 1 }                       -- Error [E0303]: non-exhaustive match (missing 'false')
-- match raw { _ -> "a"; "dead" -> "b" }          -- Error [E0304]: unreachable match arm
-- match (1, 2) { (x, 2) | (1, y) -> 0; _ -> 1 }  -- Error [E0346]: or-pattern binder mismatch
-- let (dup, dup) = (1, 2)                        -- Error [E0347]: duplicate binder 'dup'
-- match 5 { 10..5 -> 0; _ -> 1 }                 -- Error [E0348]: empty range pattern
-- match raw { str[..a, ..b] -> a; _ -> "" }      -- Error [E0349]: multiple '..' in str[...]
-- let .{ mut fixed } = .{ fixed: [1, 2] }        -- Error [E0521]: cannot bind 'mut' from immutable record
-- let (mut bad_slot, _) = ([1], [2])             -- Error [E0551]: tuple slot cannot decompose as 'mut'
```

- **Construction symmetry (`E0314`, `E0349`)**: Tight `Type.{ a, b }` unpacks named records; tight `Some(x)`, `Some(mut c)`, `Ok()`, `Rect(w, h)`, and `UserId(id)` unpack payload variants and non-record nominals (`E0314` on tuple arity mismatch; `E0349` on arbitrary expressions or `{expr}` interpolations in patterns).
- **Or-patterns & uniqueness (`E0346`, `E0347`)**: Alternatives `P1 | P2` must bind the exact same names with identical types and modes (`E0346`); duplicate binders in one alternative fail `E0347`.
- **Range patterns (`E0348`)**: `lo..hi` / `lo..=hi` require non-empty integer intervals (`lo < hi` for `..`, `lo <= hi` for `..=`, `E0348`).
- **Array & `str[...]` slices (`E0349`)**: Both `[a, ..rest, z]` and `str["pre", ..rest, "suf"]` allow at most one `..` / `..rest` segment (`E0349` on multiple `..`). In `ArrayPattern`, `..rest` binds a fresh `new`-qualified array slice preserving the subject's element modes; in `str[...]`, literals must be non-empty without `{expr}` interpolations (`E0349`) and match `s` iff `s` starts with concatenated prefixes, ends with concatenated suffixes, and `len(s) >= len(prefix) + len(suffix)`.
- **Exhaustiveness & reachability (`E0303`, `E0304`)**: `match` must cover every possible value (`E0303`; arms with an `if` guard do not count toward coverage). Unreachable or shadowed arms fail `E0304`.
- **Pattern reception (`E0402`, `E0521`, `E0551`)**: Value-type bindings forbid `ref`/`mut`/`^mut` (`E0402`); requesting `mut`/`^mut` from an immutable/`ref` subject fails `E0521`; mutable decomposition on an immutable tuple or fixed-mode sub-slot (e.g., `Rect(mut a, mut b)`) fails `E0551`. Prefix mode on `let`/`if let`/`while let`/`let ... else` (`mut`, `ref`, `^mut`, `via`) applies to the top-level bound root and unmodified leaf binders; contradictory nested `BindingModifier`s fail `E0521`/`E0357`, and `via` binders require an enclosing `via` template (`E0412`).

```ebnf
MatchExpr            ::= "match" Expression "{" [ MatchArm { Separator MatchArm } [ Separator ] ] "}"
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
ConstructorPath      ::= { "Super" "::" } { PathSegment "::" } PascalCase [ GenericArgs ]
ConstructorPattern   ::= ConstructorPath "(" [ PatternList ] ")"
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
                       | "mut" | "^mut" | "ref" | "via"
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

### Flow-Sensitive Type Narrowing

Conditions using `== None`, `!= None`, `!`, `&&`, `||`, and early-exit `if` / `while` checks narrow `?T` bindings and field paths in-place across subsequent guarded paths:

```ril
type Cell = .{ var val: ?int }

fn check_narrowing(mut cell: Cell, via hook: fn() & -> (), eff_cb: fn() @ -> (), nested: ??int) &mut -> int {
    var local: ?int = Some(10)
    if local == None {
        -- if local != None { return 0 }        -- Error [E0311]: contradictory 'None' narrowing
        return 0
    }
    let ok = local + 1                          -- Sequential flow narrowed 'local' to 'int'
    local = None
    -- let _ = local + 1                        -- Error [E0310]: 'local' narrowing invalidated by assignment

    if nested != None {
        if nested == None { return ok }         -- OK: 'nested: ??int' unwrapped one optional layer to '?int'
    }
    if cell.val != None {
        hook()
        -- let _ = cell.val + 1                 -- Error [E0533]: open-state '&' call may alias live 'cell.val'
    }
    if cell.val != None {
        eff_cb()
        -- let _ = cell.val + 1                 -- Error [E0533]: open-effect '@' call may invoke stateful handler
    }
    let snap = clone(ref cell)
    cell.val = None
    if snap.val != None { ok + snap.val } else { ok } -- OK: immutable 'snap' survives 'hook()' and 'cell' writes
}
```

- **Optional unwrapping**: `x != None` (or `!(x == None)`) narrows `x: ?T` by one optional layer to `T`; `if x == None { return ... }` narrows subsequent sequential flow to `T`.
- **Contradictory test (`E0311`)**: Testing `== None` or `!= None` when disjoint from the active optional state of a single-layer `?T` fails `E0311: ContradictoryNarrowingError` (nested `??T` unwraps one layer at a time).
- **Write invalidation (`E0310`)**: Immutable `let` paths through immutable fields narrow without depth limit. Reassigning `var`, writing an overlapping mutable path, or calling an `@Eff` whose enclosing `with` arm writes that path invalidates the narrowing (`E0310: InvalidatedNarrowingAccessError`).
- **Unknown alias / handler hazard (`E0533`)**: Across an open-state (`&`, `@&`), open-effect (`@`), or unhandled `@Eff` call—or a `^mut` write not proved disjoint from a live path (`ref` does not prove independence; `clone` into `let` does)—reading the prior live narrowing fails `E0533: AliasedNarrowingHazardError`.

---

## Functions, Closures, and Callables

### Named Function Declarations and Contrast Matrix

| Declaration form | Syntax | Phase | Effects & state |
| :--- | :--- | :--- | :--- |
| Ordinary `fn` | `fn f(...) [@Eff] [&State] -> T { ... }` | Runtime (pure core ops dual-phase) | Explicit `@Eff` & minimal `&State` (`E0510`, `E0529`, `E0612`) |
| Compile-time `meta fn` | `meta fn f(...) -> T { ... }` | Static (`TypeEval`/`MetaValue` + saturated compile-time eval) | Pure only (`E0813`); type-value/callable/resource-free (`E0812`, `E0816`) |
| Type function | `type F = \T -> <...>` | Static (`TypeEval`) | Pure only (`E0335`); returns single `Type<U>` value |
| Built-in bodyless `fn` | Bodyless `fn` in prelude `.ril` | Per built-in specification | Must match registered primitive identity & signature (`E0902`, `E0909`) |
| Foreign `.d.ril` `fn` | Bodyless `pub fn` in `.d.ril` | Runtime | Body prohibited (`E0901`); stateful host calls declare `@io` |

#### Dual-Tier Where Invariants

A bodied `fn` or `meta fn` supports two braceless `where` tiers: a signature-level `where` before `{` (visible to signature types/guards and body) and a block-level `where` at the end of `{ ... }` (body-only):

```ril
pub fn map_fallible<T, R, E>(xs: []T, step: StepFn<T, R, E>) @io -> new !<[]R, E>
where
    type StepFn<In, Out, Err> = fn(In) @io -> !<Out, Err>
{
    let mut out: []R = []
    for xs as item { Array::push(mut out, step(item)?) }
    Ok(new out)
where
    fn _helper_tag() -> int { 1 }
}
```

```ril
-- Rejected where-clause placements and scope references:
-- fn bad_braced(x: int) -> int where { type T = int } { x }        -- Error [E0120]: 'where' clauses do not use '{ ... }'
-- fn bad_sig_eff(x: int) -> int where eff E { fn op() -> () } { x } -- Error [E0704]: 'eff' prohibited in signature 'where'
-- fn bad_down() -> Wrap where type Wrap = .{ s: Inner } { Wrap.{ s: .{ n: 0 } } where type Inner = .{ n: int } } -- Error [E0705]
-- fn bad_sig_ref(cb: Cb) -> () { cb() where type Cb = fn() -> () }  -- Error [E0706]: signature references block 'where'
```

- **`SignatureWhereClause` (`E0704`, `E0702`, `E0120`)**: Braceless `where` list terminated by `{` (`where { ... }` and `pub`/`pkg` fail `E0120`). Admits `type`, `fn`, and `meta fn` (`eff`/`sub` fail `E0704`; value bindings fail `E0702`). Visible across the signature (`PipelineConstraint`, `SignatureGuard`, types) and body.
- **Signature confinement (`E0706`, `E0315`)**: Types and guards in the signature must come from `SignatureWhereClause` or an enclosing scope (`E0706` on `BlockWhereClause` references). Non-transparent local `nominal`/`opaque`/sum declarations in `SignatureWhereClause` cannot escape in the signature (`E0315`).
- **Downward isolation & uniqueness (`E0705`, `E0203`)**: `SignatureWhereClause` cannot reference `BlockWhereClause` (`E0705`); `BlockWhereClause` may reference `SignatureWhereClause`. Duplicate names across both tiers fail `E0203`.

#### Signature Guards

`SignatureGuard` (`|> [ref] guard(args)`) attaches pure fallible entry and exit guards to `RegularParam` and declaration `ReturnSpec` (`FunctionDecl`, `MetaFnDecl`, `DeclFunction`):

```ril
pub type Span = .{ lo: int, hi: int }
pub type SpanErr { Inverted; Empty }

pub fn make_span(lo |> ordered(hi), hi: int) -> new !<Span, SpanErr> |> non_empty
where
    fn ordered(lo: int, hi: int) -> new !<(), SpanErr> {
        if lo <= hi { Ok() } else { Err(SpanErr::Inverted) }
    }
    fn non_empty(s: Span) -> new !<(), SpanErr> {
        if s.hi > s.lo { Ok() } else { Err(SpanErr::Empty) }
    }
{
    Ok(Span.{ lo, hi })
}

fn test_guards() -> () {
    assert(make_span(2, 5) == Ok(Span.{ lo: 2, hi: 5 }))
    assert(make_span(5, 2) == Err(SpanErr::Inverted))
    assert(make_span(3, 3) == Err(SpanErr::Empty))
}
test_guards()
```

```ril
-- Rejected signature guards:
-- fn bad_bool_guard(x: int |> pos) -> new ?int where fn pos(n: int) -> bool { n > 0 } { Some(x) } -- Error [E0712]
-- fn bad_ret_guard(x: int |> pos) -> int where fn pos(n: int) -> new ?() { Some() } { x }         -- Error [E0713]
-- fn bad_untyped(x) -> new ?int { Some(x) }                                                       -- Error [E0544]
```

- **Parameter type omission & `meta` callables (`E0544`, `E0344`, `E0810`)**: A `RegularParam` or `MetaParam` with a `SignatureGuard` / `PipelineConstraint` may omit `: TypeExpression`, inferring its type from the first guard/constraint (`E0544` without one; `E0344` if undetermined). Callables declaring `MetaParam`s require compile-time static arguments at direct call sites (`E0814`) and cannot decay to runtime `CallableType` values (`E0810`).
- **Pure fallible guard (`E0409`, `E0712`, `E0713`)**: Guards must be pure (`E0409` on `@Eff` or mutable/capturing state) and return `!<(), E>` or `?()` (`E0712`) compatible under `?` with the enclosing function's `!<T, E_out>` or `?T` return type (`E0713`).
- **Evaluation order (`E0549`, `E0527`)**: Arguments and defaults bind left-to-right; parameter guards then run in declaration order via `(p |> [ref] guard(args))?`. On `Ok(v)` / `Some(v)` return (`Err`/`None` bypasses exit guards), return guards run via `(v |> [ref] guard(args))?`.
- **`|> ref` & authority**: `|> ref` preserves `new` qualification on `v`; reading an ended `new` parameter in a return guard fails `E0549`, and guards alone do not satisfy `E0527`.

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
                         [ ":" TypeExpression ] { SignatureGuard }
                         [ "=" Expression ]
MetaParam            ::= "meta" ( ValueName | Wildcard ) [ ":" TypeExpression ]
                         { "|>" PipelineConstraint } [ "=" Expression ]
ParameterMode        ::= "mut" | "^mut" | "ref" | "new" | "via"
ReturnSpec           ::= [ EffectAnnot ] [ StateAnnot ] "->" ReturnType { SignatureGuard }
SignatureGuard       ::= "|>" [ "ref" ] QualifiedName [ GenericArgs ] [ "(" [ GuardArgList ] ")" ]
GuardArgList         ::= GuardArg { "," GuardArg } [ "," ]
GuardArg             ::= [ ValueName ":" ] ( [ "ref" ] QualifiedName | [ "-" ] Literal )
ReturnType           ::= [ ReturnMode ] TypeExpression
ReturnMode           ::= "new"
                       | "infer"
                       | ( "ref" | "^mut" ) "(" ReturnSources ")"
ReturnSources        ::= ValueName { "|" ValueName }
```

### Callable Types and Signatures

#### Mandatory Signature Inference and Completion

The compiler infers complete effects and provenance for every callable body:
- **Named `fn` definitions**: Must faithfully spell exact unhandled `@Eff` (`E0612`), minimal concrete state clauses (`&mut`, `&^mut`, `&capture`, `&up(...)`, `&return(...)` — `E0510` missing, `E0529` excessive), and exact return modes (`new`, `ref(x)`, `^mut(x)` — `E0544`/`E0528`/`E0546`), unless `via`/`infer` encapsulates them. A named `fn` cannot unilaterally freeze away `new` qualification on a newly constructed `SharedObject` behind a plain `-> T` signature (`E0544`); whether to freeze (`let`) or mutate (`let mut`) is decided by the caller.
- **Form separation (`E0538`)**: Abstract `&up` / `&up(ref)` are prohibited on named `fn` declarations, and concrete `&up(x)` is prohibited on `CallableType` (`E0538`).
- **Anonymous closures (`\... -> ...`)**: Infer their exact callable signature automatically; optional written `@Eff` / `&State` / `: Type` annotations constrain inference.

#### Closed and Open Effect and State Sets

Omitted sets are closed empty; `@`, `&`, and `@&` open effect/state bounds on `CallableType` in parameters, record fields, and collection elements (`E0547` on named or anonymous definitions). Open markers never erase effects or state: the compiler retains and propagates the underlying callables' exact effects, state obligations, and provenance across bindings, record/collection storage, and module interfaces (`K-IFACE`, unioned across branches and collections), charging them at every invocation site.

Access modes stay strictly orthogonal to `@`/`&`/`@&`: plain fields and bindings remain deeply immutable (`E0535` rejects `&up` mutable captures while admitting arbitrary `@Eff` on pure/immutable closures); storing a mutable `&up` closure in a record field or collection requires a writable mode (`mut`, `^mut`, `M`, or `via`), and higher-order parameters accepting `&`/`@&` callables declare `via` (or `mut`/`^mut`) explicitly.

```ril
type PureFn   = fn(int) -> int             -- Closed empty effects, closed pure state
type IoFn     = fn(str) @io -> ()          -- Closed {io}, closed pure state
type ReadObs  = fn() &up(ref) -> int       -- Pure effects, read-only closure env (invocable via ref)
type MutStep  = fn() &up -> int            -- Pure effects, mutable closure env (requires mut/^mut path)
type AnyEff   = fn() @ -> ()               -- Open effect set, closed pure state
type AnyState = fn() & -> ()               -- Closed empty effects, open state/provenance
type AnyCall  = fn() @& -> ()              -- Open effects and open state/provenance
```

| Callable annotation | Effects (`@`) | State & provenance (`&`) |
| :--- | :--- | :--- |
| *(omitted)* | Closed empty | Closed pure |
| `@io` | Closed `{io}` | Closed pure |
| `&up(ref)` | Closed empty | Read-only captured closure env (live observer invoked via `ref`; pure callables matching `&up(ref)` remain plain) |
| `&up` | Closed empty | Mutable/abstract closure env (requires `mut`/`^mut` path, `E0520`) |
| `@` | Open effect set (tracked & charged at call) | Closed pure (live narrowings still reject handler writes, `E0533`) |
| `&` | Closed empty | Open state/provenance set (tracked & charged at call; orthogonal to access mode) |
| `@&` | Open effect set (tracked & charged at call) | Open state/provenance set (tracked & charged at call; orthogonal to access mode) |

#### Callable Compatibility

```ril
type Cell = .{ var v: int }
type Obs  = fn() &up(ref) -> int
type Step = fn() &up -> int

fn read_obs(ref f: Obs) -> int { f() }         -- OK: '&up(ref)' is read-only
fn run_step(mut f: Step) &mut -> int { f() }   -- OK: '&up' invoked through 'mut' path
```

```ril
-- Rejected callable signatures and conversions:
-- fn bad_step(ref f: Step) -> int { f() }     -- Error [E0520]: '&up' requires 'mut' or '^mut' callable path
-- pub fn len(x: int) -> int                   -- Error [E0909]: built-in signature mismatch in prelude
-- fn bad_open() @ -> () {}                    -- Error [E0547]: open '@' marker prohibited on named 'fn'
-- fn bad_ret(ref a: []int) -> []int { a }     -- Error [E0544]: missing 'ref(a)' return mode annotation
-- fn bad_new_omit() -> []int { [1, 2] }       -- Error [E0544]: missing 'new' return mode annotation
-- let pure_cb: fn() -> () = \-> println("hi") -- Error [E0534]: '@io' incompatible with pure 'fn() -> ()'
-- let mode_cb: fn([]int) -> () = \mut xs: []int -> Array::push(mut xs, 1) -- Error [E0407]: mode 'mut' vs plain
-- let idle_cb = \mut _xs: []int -> ()         -- Error [E0527]: wildcard does not waive 'mut' use
```

Under `MatchCallable`, a callable of actual signature $C_{\text{act}}$ matches expected `CallableType` $C_{\text{exp}}$ (`E0534` on signature/return-mode mismatch, `E0407` on parameter mode mismatch) iff:
1. **Types & modes**: Parameter count matches (`E0314`), parameter types are contravariant, return type is covariant, concrete parameter modes match (`E0407`; `mut`/`^mut` definitions still satisfy `E0527`), and return modes/sources satisfy $C_{\text{exp}}$ (`E0534`; a caller's plain `-> T` target may receive a freezable `-> new T` result).
2. **Effects**: Every effect in $C_{\text{act}}$ appears in $C_{\text{exp}}$ (or is covered by an `@SupEff` spread in $C_{\text{exp}}$, unless $C_{\text{exp}}$ is effect-open via `@` or `@&`).
3. **State & captures**: Every non-pure state/capture obligation in $C_{\text{act}}$ is permitted by $C_{\text{exp}}$ (`&` / `@&` opens state obligations):
   - `&up(ref)` admits pure or read-only observer closures callable via `ref`.
   - `&up` admits mutable closure environments; invoking an `&up` callable requires a `mut` or `^mut` path and charges `&mut` when the callable is a formal parameter.
   - Pure module constants, pure immutable captures, and pure stateless lexical `fn` handlers reduce to empty state; return-source relations remain checked.

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
CallableStateClause ::= "&up" | "&up(" "ref" ")" | "&mut" | "&^mut" | "&capture" | ReturnDependencyGroup
```

### Return Construction, Access Modes, and Sources

| Return form | Meaning & static check |
| :--- | :--- |
| `-> T` | Value type, `meta fn` snapshot, or existing deeply immutable `SharedObject` snapshot (`E0544` if all normal return paths of a named `fn` produce a `new`-qualified `SharedObject`; `E0528`/`E0535` if live or writable) |
| `-> new T` | `new`-qualified root with no independent surviving aliases into `new` subgraphs (`E0546`); target selects modes for `new` subgraphs while preserving contained existing sources |
| `-> ref(x \| y) T` | Read-only view rooted in formal `x` or `y`'s call-entry graph (`E0545` on local or temporary sum-subset wrapper) |
| `-> ^mut(x \| y) T` | Shared writable result rooted in `^mut` formal `x` or `y`'s call-entry graph (`E0545` on call-scoped `mut`; needs no duplicate `&^mut`, `E0529`) |
| `&return(x, ref y, ^mut z)` | Records contained existing immutable, live read-only, and shared writable object sources; normalized metadata maps each source to its return paths |

**1. Root returns (`ref(...)` and `-> new`)**:

```ril
type Node = .{ var val: int }

fn pick_ref(cond: bool, ref a: Node, ref b: Node) -> ref(a | b) Node {
    if cond { a } else { b }
}
fn make_nodes() -> new []Node { [Node.{ val: 1 }, Node.{ val: 2 }] }
fn make_staged() -> new []Node {
    let mut xs: []Node = [Node.{ val: 1 }]
    Array::push(mut xs, Node.{ val: 2 })
    new xs
}
fn edit_factory(factory: fn() -> new []Node) -> int {
    let mut xs: [mut]Node = factory()         -- OK: 'new' qualification survives callable storage
    xs[0].val += 1
    xs[0].val
}

fn test_returns() -> () {
    let snap: []Node = make_nodes()            -- Freezes graph as immutable []Node
    let mut edit: [mut]Node = make_nodes()     -- Receives 'new' graph as [mut]Node
    edit[0].val = 10
    let mut shared: [^mut]Node = make_nodes()
    shared[0].val += 1
    assert(snap[0].val == 1 && edit[0].val == 10 && edit_factory(make_staged) == 2)
}
test_returns()
```

**2. Contained existing sources (`&return(...)`)**:

```ril
type Cell = .{ var value: int }
type Shelf = .{ mut rows: [^mut]Cell }

fn shared_shelf(^mut cell: Cell) &^mut &return(^mut cell) -> new Shelf {
    Shelf.{ rows: [^mut cell] }
}
fn wrap_snapshot(cell: Cell) &return(cell) -> new []Cell { [cell] }
fn wrap_view(ref cell: Cell) &return(ref cell) -> new [ref]Cell { [cell] }
fn wrap_option(cell: Cell) &return(cell) -> new ?Cell { Some(cell) }
fn id_new(new xs: []Cell) -> new []Cell { new xs }

fn test_contained_sources() -> () {
    let mut cell = Cell.{ value: 0 }
    let mut shelf = shared_shelf(^mut cell)
    shelf.rows[0].value += 1
    let mut next = new shelf
    next.rows[0].value += 1
    assert(cell.value == 2)                  -- Independent existing source remains valid and shared

    let snapshot = Cell.{ value: 5 }
    let wrapped = wrap_snapshot(snapshot)    -- OK: every existing boundary is deeply immutable
    let mut copied: [mut]Cell = clone(wrapped)
    copied[0].value += 1
    assert(snapshot.value == 5 && len(id_new(new [Cell.{ value: 9 }])) == 1 && copied[0].value == 6)
}
fn read_wrapped(cell: Cell) -> new ?int {
    let payload = wrap_option(cell)?         -- Existing immutable payload, despite the new Some wrapper
    Some(payload.value)
}
test_contained_sources()
```

**3. Rejected return and provenance cases**:

```ril
-- Rejected root and contained-source returns:
-- fn bad_wrap(n: Node) -> new []Node { [n] }                         -- Error [E0510]: missing '&return(n)'
-- fn bad_src(mut a: Node) &mut -> ^mut(a) Node { a.val += 1; a }     -- Error [E0545] / [E0528]
-- fn bad_new(ref a: Node) -> new Node { a }                          -- Error [E0546]: 'ref' is not 'new'-qualified
-- type WrongShelf = .{ mut rows: [mut]Cell }
-- fn bad_shelf(^mut c: Cell) &^mut &return(^mut c) -> new WrongShelf { WrongShelf.{ rows: [^mut c] } } -- Error [E0357]
-- let bad_factory: fn(Cell) -> new []Cell = wrap_snapshot            -- Error [E0534]: existing source cannot be erased
-- let frozen = shared_shelf(^mut cell)                               -- Error [E0535]: surviving outside writer
-- let mut bad_view: [mut]Cell = wrap_view(ref cell)                  -- Error [E0522]: existing read-only element
-- let _ = id_new(new wrap_snapshot(snapshot))                        -- Error [E0548]: non-'via' '-> new' rejects contained sources
-- let mut bad: [mut]Cell = wrap_snapshot(snapshot)                   -- Error [E0522]: existing element cannot gain writes
-- let mut bad_opt = wrap_option(cell)?                               -- Error [E0520]: payload itself is not new
```

- **Contained existing sources (`E0510`, `E0545`)**: Named definitions declare every contained existing object source in `&return(...)` (`E0510` if omitted); with none, `-> new` promises a complete `new` graph. `&return(x)` requires a deeply immutable source (`E0545`); value copies and plain `-> T` returns need no `&return(...)`.
- **`new` parameter forwarding (`E0548`)**: A non-`via` `new x: T` parameter cannot supply existing-source boundaries to a `-> new R` result (`E0548` at call sites when `x` carries contained existing sources). Forward arbitrary contained sources with `fn f<T>(via x: T) -> infer R`.
- **Deep source tracking (`E0546`, `E0528`)**: Sources are tracked through arbitrary nesting, cycles, and aliases; projection, pattern decomposition, `inner`, `?`, and sum re-wrapping preserve the selected subgraph's qualification.
  - An outside path back into a `new` subgraph invalidates `new` qualification (`E0546`); escalating authority on a returned existing source fails `E0528`.

### Parameter Modes, Caller Obligations, and Defaults

Parameters forbid `var` (`E0403`; copy into a local `var` if slot replacement is needed). Concrete calls spell explicit argument mode markers (`E0405` if omitted, `E0406` if mismatched, `E0410` if `mut`/`^mut` targets a non-addressable expression):

| Formal parameter | Call-site marker | Authority & obligation |
| :--- | :---: | :--- |
| `x: T` | `expr` or `\|>` | Deeply immutable snapshot or value copy (`E0535` on live writer) |
| `ref x: T` | `ref expr` or `\|> ref` | Call-scoped read-only access to a shared-object source (`E0401` on value type `T`) |
| `mut x: T` | `mut path` or `\|> mut` | Call-scoped write access (accepts `mut` or `^mut` paths); requires reachable write (`E0527`, `&mut`) and source-overlap checks (`E0523`, `E0524`), and grants no retained writer |
| `^mut x: T` | `^mut path` or `\|> ^mut` | Shared writable binding; requires reachable retention beyond call scope (`E0527`; `&^mut` beyond root return) |
| `new x: T` | `new expr` or `\|> new` | Receives a `new`-qualified result (`E0548` on an unqualified root, or when a non-`via` `-> new` callee would erase `expr`'s contained existing sources; ends `expr` with `E0549`; `E0411` on value types). Inside the callee, `x` is a pinned `new`-qualified binding: readable directly (`x.field`), hand-offable via `new x`, and rebound via `let mut o = new x` for local writes |
| `via x: T` | Mode-dependent | Instantiates static mode template from caller's supplied mode |

```ril
type Node = .{ var val: int }
fn bump_node(mut n: Node) &mut -> () { n.val += 1 }
fn take_node(new n: Node) -> int { n.val }

fn test_params() -> () {
    let mut n0 = Node.{ val: 5 }
    bump_node(mut n0)
    let mut s0 = Node.{ val: 1 }
    let ^mut sh = s0
    bump_node(mut sh)                   -- OK: call-scoped 'mut' parameter accepts '^mut' path
    assert(s0.val == 2)
    assert(take_node(new n0) == 6)      -- OK: the completed mutable call did not retain an alias
}
test_params()
```

```ril
-- Rejected parameter declarations and call sites:
-- bump_node(n0)                        -- Error [E0405]: missing 'mut' marker at call site
-- bump_node(ref n0)                    -- Error [E0406]: argument mode 'ref' does not match 'mut'
-- bump_node(mut Node.{ val: 1 })       -- Error [E0410]: 'mut' requires an addressable writable path
-- bump_node(mut n0, 1)                 -- Error [E0314]: arity mismatch (expected 1, got 2)
-- let _ = n0.val                       -- Error [E0549]: source path ended after 'new n0'
-- fn bad_var(var x: int) -> () { x = 1 }  -- Error [E0403]: 'var' parameter prohibited
-- fn bad_new_val(new x: int) -> int { x } -- Error [E0411]: 'new' prohibited on value type 'int'
```

#### Default Parameters and Named Arguments

```ril
fn connect(host: str, port: int = 8080, tls: bool = true) -> str {
    "{host}:{port} (tls={tls})"
}
fn step_from(start: int, delta: int = start) -> int { start + delta }

fn test_defaults() -> () {
    assert(connect("db.local", tls: false) == "db.local:8080 (tls=false)")
    assert(step_from(5) == 10)
}
test_defaults()
```

```ril
-- Rejected defaults and named arguments:
-- connect("db.local", host: "dup")       -- Error [E0325]: parameter 'host' bound twice
-- connect("db.local", prt: 90)           -- Error [E0339]: unknown parameter label 'prt'
-- fn bad_mut_def(mut n: Node = Node.{ val: 0 }) &mut -> () { n.val += 1 } -- Error [E0404]
-- fn bad_fwd_def(a: int = b, b: int = 1) -> int { a + b }                 -- Error [E0408]
-- fn bad_io_def(s: str = { println("x"); "a" }) @io -> str { s }          -- Error [E0409]
```

- **Permitted default modes (`E0404`)**: Plain, `ref`, and `meta` parameters on `FunctionDecl`, `MetaFnDecl`, and `AnonFnExpr` may declare `= default_expr`; defaults on `mut`, `^mut`, `new`, or `via` parameters fail `E0404`.
- **Default scope & purity (`E0408`, `E0409`, `E0910`, `E0510`)**:
  - Defaults may reference earlier plain immutable or `meta` parameters (`ref b: T = a` may also alias an earlier `ref a: T`). Self/forward references fail `E0408`; `@Eff`, reading live `ref` fields, referencing `mut`/`^mut`/`new` parameters, or mutable/foreign state fails `E0409`.
  - Exported callables require referenced module bindings to satisfy `E0910`; publishing a default closure capturing an earlier parameter charges `&capture` at the caller (`E0510`).
- **Evaluation & binding (`E0325`, `E0339`, `E0314`, `E0338`)**: Explicit arguments evaluate left-to-right in written order, then omitted defaults in parameter order.
  - Positional arguments bind the next unbound parameter; `label: expr` binds `label` (`E0339` unknown, `E0325` duplicate, `E0314` missing required, `E0338` non-callable).
- **`CallableType` boundary (`E0314`)**: `CallableType` carries optional parameter labels by position and strips default expressions (`E0314` when omitted through a `CallableType` value).

### Anonymous Functions, Trailing Closures, and Projection Accessors

Anonymous closures (`\... -> ...`) and shorthand projection accessors (`\.field`, `\?.field`) attach cleanly as trailing arguments after `(...)` or directly after a callee:

```ril
type Dept = .{ name: str, code: (str, int) }
type Org  = .{ title: str, dept: ?Dept }

fn with_tx<T>(mut log: []str, via body: fn(mut []str) @& -> !<T, str>) &mut -> new !<T, str> {
    Array::push(mut log, "begin")
    let out = body(mut log)?
    Array::push(mut log, "commit")
    Ok(out)
}

fn test_closures_and_accessors() -> new !<int, str> {
    let orgs = [
        Org.{ title: "Core", dept: Some(Dept.{ name: "Infra", code: ("INF", 10) }) },
        Org.{ title: "Labs", dept: None },
    ]
    assert((orgs |> Array::map \.title) == ["Core", "Labs"])
    assert((orgs |> Array::map \.dept?.code.1) == [Some(10), None])
    assert(([1, 2, 3] |> Array::map \x -> { x * 2 } |> Array::filter \x -> { x > 2 }) == [4, 6])

    let mut log: []str = []
    let code = log |> mut with_tx \mut entries -> {
        Array::push(mut entries, "insert")
        Ok(200)
    }?
    assert(log == ["begin", "insert", "commit"])
    Ok(code)
}
assert(test_closures_and_accessors() == Ok(200))
```

- **Closure Body Termination**: When `{` immediately follows `->`, `AnonFnBody` parses as a self-delimited `Block` ending at `}`; non-block bodies parse as `Expression`.
- **Trailing Closures**: A `CallExpr` or `PipelineStep` may pass its final callable argument as a trailing `AnonFnExpr` or `AccessorExpr` after `(...)`—or omit `()` when no other arguments remain (`absorb_panic \-> { ... }`, `Fiber::scope \mut s -> { ... }`). Postfix `?` and outer `|>` attach directly after a block-bodied trailing closure.
- **Shorthand Projection Accessors (`\.field`, `\.0`, `\?.field`)**: Desugar to unary pure closures (`\x -> x.field`, `\x -> x.0`, `\x -> x?.field`) over records and tuples (`E0336` unknown field, `E0312` tuple index out of bounds, `E0337` on sums, collections, or primitives). Any `?.` segment lifts the result to `?T`.

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

### Closures and Lexical Environments

Closures infer captures from body uses while preserving each retained source's concrete mode and provenance:

```ril
type CounterCell = .{ var value: int }
type Step = fn() &up -> int

fn make_adder(k: int) &capture -> new fn(int) -> int { \x -> x + k }

fn make_counter(^mut cell: CounterCell) &capture &^mut &return(^mut cell) -> new Step {
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

- **Factory `&capture` (`E0510`)**: Returning or storing a newly created closure that captures any enclosing runtime local, parameter, or stateful lexical handler requires `&capture` on the enclosing named `fn`.
- **Local writable captures (`E0510`)**: Binding a newly created closure that captures an outer `let mut` local in writable mode into a local variable creates a second writer alongside that local and requires explicit `let ^mut` (inline non-stored callbacks such as `derive` arguments or a single `with` arm hold scoped access directly).
- **Callable targets**: Pure immutable captures still match pure `fn(...) -> ...` targets; live `ref` observer closures match `&up(ref)`; mutable closures match `&up`.

---

## State and Provenance Tracking

### Local State Containment, Parameter Mutation, and Sharing

```ril
type Node = .{ var val: int }
fn reset_node(new c: Node) -> int {
    let mut o = new c
    o.val = 0                              -- OK: write to handed-off 'new' subgraph stays local
    o.val
}
fn bump_shelf(new s: .{ mut rows: [^mut]Node }) &mut -> () {
    let mut o = new s
    o.rows[0].val += 1                     -- OK: mutates caller-surviving '^mut' constituent
}
assert(reset_node(new Node.{ val: 9 }) == 0)
-- fn excess_new(new c: Node) &mut -> int { let mut o = new c; o.val = 0; o.val } -- Error [E0529]
-- fn excess_mut(ref c: Node) &mut -> int { c.val }                               -- Error [E0529]
-- fn dup_share(^mut c: Node) &^mut -> ^mut(c) Node { c }                         -- Error [E0529]
```

- **Local Containment**: Writes and `^mut` sharing confined to non-escaping local `var` / `let mut` allocations—and writes confined to the handed-off `new` subgraphs of a `new` parameter—stay local; the function remains outwardly pure.
- **`&mut` (`E0510`)**: Required on named functions that may mutate caller-surviving writable state: a `mut` parameter, a `^mut` parameter, or a `^mut` constituent reachable inside a `new` parameter.
- **`&^mut` (`E0510`)**: Required when a `^mut` parameter (or locally allocated shared root) is retained into another parameter, escaping closure environment, or escaping non-root structure (root `-> ^mut(x) T` already accounts for its own retention).
- **`&capture` (`E0510`)**: Required when a named `fn` returns or stores a newly created closure environment capturing any enclosing runtime local, parameter, or stateful lexical handler (module/`sub` constants need zero `&capture`).
- **Contained Immutable Sources**: `&return(x)` adds no state effect and remains part of the return provenance.
- **Minimal Annotations (`E0529: ExcessiveStateAnnotationError`)**: Named `fn` declarations must not spell `&mut`, `&^mut`, `&capture`, `&up(...)`, or `&return(...)` clauses not actually exercised by the body (including redundant `&^mut` alongside bare root `-> ^mut(x) T`).

### State Groups and Captured Layers

Block-local named `fn` declarations in `BlockWhereClause` spell `&up(...)` for captured outer local bindings, while pure module/`sub` constants require no annotation:

```ril
let global_factor = 3                  -- Pure module constant

fn scale_all(xs: []int, offset: int) -> new []int {
    var total = 0
    let mut out: []int = []
    for xs as x {
        let scaled = transform(x)
        add_total(scaled)
        Array::push(mut out, scaled)
    }
    assert(total == 17)
    new out
where
    fn transform(x: int) &up(offset) -> int {
        x * global_factor + offset     -- global_factor needs no '&up'; outer local 'offset' uses '&up(offset)'
    }
    fn add_total(n: int) &up(var total) -> () {
        total += n                     -- Reassigning outer 'var' spells '&up(var total)'
    }
    -- fn bad_up(x: int) &up(ghost) -> int { x }  -- Error [E0538]: unknown outer source 'ghost' in '&up(...)'
    -- fn idle_up(x: int) &up(offset) -> int { x } -- Error [E0529]: excessive '&up(offset)' not read by body
}
assert(scale_all([1, 2], 4) == [7, 10])
```

- **Local capture forms (`&up(...)`, `E0538`, `E0529`)**: List captured outer bindings with their mode: `&up(limit)` (plain/`var` read), `&up(var acc)` (`var` reassignment), `&up(ref view)`, `&up(mut buf)`, `&up(^mut shared)`. Empty `&up()`/`&return()` or malformed groups fail `E0538`; unused items fail `E0529`.
- **Module & `sub` constants (`E0906`)**: Module-level and `sub`-level functions never carry `&up(...)` because top-level forbids mutable or live state (`E0906`) and reading pure `let` / `meta let` constants requires no state annotation.

```ebnf
StateAnnot            ::= StateClause { StateClause }
StateClause           ::= "&mut"
                        | "&^mut"
                        | "&capture"
                        | CapturedStateGroup
                        | ReturnDependencyGroup
CapturedStateGroup    ::= "&up(" StateItemList ")"
StateItemList         ::= StateItem { "," StateItem } [ "," ]
StateItem             ::= [ StateMode ] ValueName
StateMode             ::= "var" [ "mut" | "^mut" | "ref" ]
                        | "mut" | "^mut" | "ref"
ReturnDependencyGroup ::= "&return(" ReturnDependencyList ")"
ReturnDependencyList  ::= ReturnDependency { "," ReturnDependency } [ "," ]
ReturnDependency      ::= [ "ref" | "^mut" ] QualifiedName
```

### Exclusivity and Authority-Escalation Matrix

At every call and assignment, Ril checks potentially overlapping mutable/live source sets (immutable snapshots carry zero mutable/live sources). Concrete access modes match exactly; `^mut` arguments and stored elements require `^mut` targets. Source-overlap checking does not relax mode matching.

Two explicitly shared `^mut` parameters may receive the same object. Each parameter still requires surviving retention through its own provenance. A nested `mut` borrow can use one of these parameters when the nested call has no overlapping participants.

Borrowing a container as `mut` preserves the mode of an existing `^mut` member. Borrowing that member directly as a `mut` argument requires exclusive access to the member's reachable writers during the call.

| Violation | Diagnostic |
| :--- | :---: |
| Writing through plain immutable or `ref` access, or binding immutable/`ref` data as `mut`/`^mut` | `E0520` |
| Destructuring pattern requesting `mut`/`^mut` from an immutable/`ref` subject or immutable field | `E0521` |
| Upgrading existing immutable/`ref`/`^mut` container or sum constituents to unshared `[mut]`/`mut` modes | `E0522` |
| Overlapping `mut` with `mut`, `^mut`, `new` (carrying `^mut` sources), or an active `with` write hold | `E0523` |
| Overlapping `mut` with `ref`, plain observation, `new` (carrying `ref` sources), or an active `with` hold | `E0524` |
| Mutating a collection during `for` iteration (directly or via an active `with` handler) | `E0526` |
| Returning `mut` / `^mut` / `new` authority from immutable/`ref` or call-scoped `mut` sources | `E0528` |

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
    -- swap_add(mut x, mut x)              -- Error [E0523]: overlapping mut-mut sources
    -- let _ = take_shared(mut x, new [^mut x]) -- Error [E0523]: 'mut' overlaps 'new' carrying '^mut x'
    -- let _ = observe_mut(mut x, ref x)   -- Error [E0524]: overlapping mut-ref hazard
    -- let mut bad_elems: [mut]Box = [Box.{ n: 1 }] |> \xs: []Box -> xs -- Error [E0522]: container element mode escalation
    let snap = Box.{ n: 7 }
    let mut left: []Box = [snap]
    let mut right: []Box = [snap]
    Array::push(mut left, snap)
    Array::push(mut right, snap)           -- OK: shared immutable snapshot has no live/mutable source
    let mut y = Box.{ n: 3 }
    assert(len(ref left) == 2 && take_shared(mut x, new [^mut y]) == 6 && y.n == 6)
    let mut items = [1, 2, 3]
    Array::push(mut items, 4)
    -- for ref items as v { Array::push(mut items, v) } -- Error [E0526]: mutating 'items' during 'for' iteration
}
test_exclusivity()
```

---

## Scoped Effects, Panic Containment, and Concurrency

### Effect Declarations and Handlers

Scoped effects declare direct `fn` operations dispatched lexically to enclosing `with` handlers and returning directly to the call site (no continuation capture):

```ril
eff Clock { fn now_ms() -> int }
eff Log {
    fn info(msg: str) -> ()
    fn warn(msg: str) -> ()
}

fn fixed_clock() -> int { 1700 }

fn audit_event(name: str) @Clock @Log -> str {
    let ts = Clock::now_ms()
    Log::info("{ts}:{name}")
    "{ts}:{name}"
}

fn test_audit() -> () {
    let mut lines: []str = []
    let mut warns: []str = []
    let ^mut step = \msg: str -> Array::push(mut warns, "warn:{msg}")
    with {
        Clock::now_ms = fixed_clock            -- Named fn bound directly
        Log::info = \msg -> Array::push(mut lines, msg)
        Log::warn = mut step                   -- Block-scoped write hold on '&up' variable
    }
    let res = audit_event("login")
    Log::warn("retry")
    assert(res == "1700:login" && lines == ["1700:login"] && warns == ["warn:retry"])
}
test_audit()
```

```ril
-- Rejected effect labels, handler arms, and active-hold conflicts:
-- with { Clock::now_ms = \-> 1; Clock::now_ms = \-> 2 } -- Error [E0622]: duplicate handler arm in single 'with'
-- with Array::len = \_ -> 0                             -- Error [E0621]: module function is not an 'eff' operation
-- with Log::warn = step                                 -- Error [E0405]: '&up' variable requires 'mut'/'^mut'/'new'
-- let frozen: []str = new lines                         -- Error [E0535]: active 'with' write hold on 'lines'
-- for ref lines as s { Log::info(s) }                   -- Error [E0526]: '@Log' handler mutates 'lines' during iteration
-- fn bad_eff() @int -> () {}                            -- Error [E0620]: 'int' is not a declared effect label
-- fn bad_mod_eff() @Fiber -> () {}                      -- Error [E0620]: 'Fiber' is a module; write '@fiber'
```

- **Evaluation & Scope (`E0120`, `E0412`, `E0538`)**: `with` installs its arms for the remainder of the enclosing block (`with {}` fails `E0120`; `EffectOpDecl` forbids `via`/`infer` `E0412` and `&up(...)` `E0538`).
  - Each arm's RHS evaluates once top-to-bottom in the **outer** handler environment before all arms take effect simultaneously; holds and `new` handoffs from earlier arms apply before later arms evaluate (`E0535`/`E0548`/`E0549`).
- **Callable Compatibility (`E0407`, `E0534`)**: Each arm checks its RHS via `MatchCallable` against `fn(OpParams) @ &up [Op.StateAnnot] -> Op.ReturnType`: outer `@` and closure `&up`/`&up(ref)` are open, while `Op`'s parameter modes (`E0407`), return mode, and parameter-level `&mut`/`&^mut`/`&return(...)` stay exact (`E0534`).
  - Installing a handler unconditionally charges its outward `@Eff`, `&mut`, and `E0527` obligations.
- **Arm RHS Mode Reception & Active Holds**: Leading `mut`/`ref`/`^mut`/`new` on an arm RHS parses as `ArgumentMode`. Active holds block freezing or `new` handoff (`E0535`/`E0548`) and overlapping mutation (`E0523`/`E0524`/`E0526`/`E0537`):

| Arm RHS form | Accepted callables | Active hold & escape rules |
| :--- | :--- | :--- |
| *(omitted)* | Pure/stateless `fn`, `where`-local `fn`, newly constructed `new` callables (`\... -> ...`, factory calls) | Activates holds on `&up(...)` of `where`-local `fn`; rejects bare `&up` variables (`E0405`/`E0520`) |
| `ref expr` | `&up(ref)` read-only observer callable | Establishes a block-scoped read hold |
| `mut path` | Mutable `&up` callable variable/path | Establishes a block-scoped write hold (`E0528`/`E0604` on escape) |
| `^mut path` | Shared writable `&up` callable path | Retains shared write authority (`E0510`/`E0528` on call-scoped `mut`; escaping `@Op` closures record `&capture &^mut &return(^mut path)`) |
| `new expr` | `new`-qualified callable | Transfers `new` qualification into the handler slot (`E0549`) while keeping active holds on contained existing sources |

- **Spreading, Generic Effects & Validation (`E0620`–`E0622`, `E0313`)**: `..SubEff` splices an accessible `eff`'s operations into `SupEff` (`E0620` non-effect, `E0313` cycle, `E0622` signature conflict); `@SupEff` covers `@SubEff`, and spliced operations share identity (`SupEff::op` and `SubEff::op` denote the same operation in `with`, so handling both in one `with` fails `E0622`). Distinct generic effect instantiations (`State<int>` vs. `State<str>`) are distinct effect labels handled independently. Arms must target declared `eff` operations (`E0621` on ordinary `fn` or `@io`/`@fiber`) without duplicates per `with` (`E0622`).
- **Handling & Capture (`E0612`, `E0618`, `E0604`)**: Covering all operations invoked by a callee (or abstract `@Eff` parameter) handles `@Eff` (`E0612` if uncovered; block-local `eff` fails `E0618` if unhandled).
  - Closures created inside `with` capture active handlers for residual `eff` ops (`&capture`/`&up` when stateful; pure stateless `fn` handlers add no state). Scoped `use` resources and `Task` handles cannot escape via handler capture (`E0604`).

```ebnf
EffectDecl         ::= { MetaAttr } [ Visibility ] "eff" PascalCase [ GenericParams ]
                       "{" [ EffectMemberList ] "}"
EffectMemberList   ::= EffectMember { Separator EffectMember } [ Separator ]
EffectMember       ::= EffectSpread | EffectOpDecl
EffectSpread       ::= ".." TypeReference
EffectOpDecl       ::= { MetaAttr } "fn" ValueName "(" [ ParameterTypeList ] ")" [ StateAnnot ] "->" ReturnType
EffectAnnot        ::= EffectClause { EffectClause }
EffectClause       ::= "@" ( SystemEffect | EffectIdentifier )
SystemEffect       ::= "io" | "fiber"
EffectIdentifier   ::= { "Super" "::" } { PathSegment "::" } PascalCase [ GenericArgs ]
EffectOperationRef ::= { "Super" "::" } { PathSegment "::" } PascalCase [ GenericArgs ] "::" ValueName
WithStatement      ::= "with" HandlerSpec
HandlerSpec        ::= HandlerArm
                     | "{" HandlerArm { Separator HandlerArm } [ Separator ] "}"
HandlerArm         ::= EffectOperationRef "=" [ ArgumentMode ] Expression
```

### Built-in System Effects

The prelude predeclares two lowercase system effect labels (`@io` and `@fiber`), keeping `PascalCase` module bindings (`use ril/io`, `use ril/fiber`, `use ril/channel`) collision-free. Non-effect names after `@` fail `E0620`, and targeting `@io` or `@fiber` in `with` fails `E0621`.

| System effect | Purpose & handling boundary |
| :--- | :--- |
| `@io` | Host I/O, timers, filesystem/network access, and stateful `.d.ril` calls; serviced by the host runtime on `fn main` |
| `@fiber` | Cooperative fiber suspension, channel waiting, structured task scopes, and cancellation checkpoints; serviced on `fn main` or run and handled deterministically by `Fiber::run` |

### Panic Absorption with absorb_panic

`absorb_panic` contains synchronous defects behind a panic-isolation boundary, running active `use` cleanup functions inside the protected closure before returning `Err(PanicError::Panicked(info))`:

```ril
-- File: ril/prelude.ril
pub opaque type PanicInfo = str
pub type PanicError { Panicked(PanicInfo) }

pub fn panic_message(info: PanicInfo) -> str
pub fn absorb_panic<T>(via action: fn() @& -> infer T) -> infer !<T, PanicError>
```

```ril
fn parse_header(parts: []str) -> str { parts[1] }

fn isolated_parse(parts: []str) -> new !<str, PanicError> {
    absorb_panic \-> parse_header(parts)
}

fn test_absorb() -> () {
    assert(isolated_parse(["k", "v"]) == Ok("v"))
    let Err(PanicError::Panicked(info)) = isolated_parse(["only_one"]) else { panic("expected panic") }
    assert(len(panic_message(info)) > 0)
    let mut ext = [1, 2]
    Array::push(mut ext, 3)
    -- let _ = absorb_panic \-> Array::push(mut ext, 4) -- Error [E0608]: panic-isolation violation on outer 'mut' access
}
test_absorb()
```

- **Panic isolation (`E0608`)**: `action` must not observe or mutate outer `var`/`mut`/`^mut`/`ref` state, hand off outer `new` channel endpoints (`Sender`/`Receiver`), access foreign `.d.ril` `opaque` handles, emit unhandled effects (including `@io`/`@fiber`) or stateful outer `with` handlers, or leak mutable/`use` captures.
- **Permitted local state**: Confined local `var` / `let mut` / `use` state and pure stateless outer or local `with` handlers are allowed inside `action`.
- **Sealed `PanicInfo` (`E0301`, `E0308`, `E0810`)**: `PanicInfo` is an opaque prelude type (`E0301` on direct construction, `E0308` on representation access); `panic_message(info)` extracts the diagnostic message at runtime (`E0810` in static evaluation).
- **Double panic**: If a `use` cleanup function panics while unwinding an earlier panic, the program triggers immediate uncatchable termination (abort) without returning `Err`.

### Structured Fiber Concurrency and Channels

`ril/fiber` provides structured cooperative task scopes using scope-bound `Scope` and `Task<T>` handles (checked under confinement identically to `Draft<T>`), alongside typed MPSC channels in `ril/channel`:

```ril
use ril/fiber
use ril/channel

fn sum_pipeline(limit: int) @fiber -> int {
    Fiber::scope \mut s -> {
        let Channel::ChannelPair.{ mut tx, mut rx } = Channel::bounded(16)
        let mut producer = Fiber::spawn(mut s) \-> {
            use mut sender = new tx
            for 1..=limit as i {
                match Channel::send(mut sender, i * i) {
                    Ok()   -> ()
                    Err(_) -> break
                }
            }
        }
        var total = 0
        while let Some(v) = Channel::recv(mut rx) {
            total += v
        }
        Fiber::join(mut s, new producer)
        total
    }
}
assert(Fiber::run(\-> sum_pipeline(4)) == 30)
```

```ril
-- Rejected cross-fiber captures and non-new channel sends:
-- let snap_xs = [1, 2]
-- let _ = Channel::send(mut tx, snap_xs)              -- Error [E0548]: shared snapshot requires 'clone(snap_xs)'
-- var shared_cnt = 0
-- let _ = Fiber::spawn(mut s) \-> { shared_cnt += 1 } -- Error [E0601]: cannot capture outer 'var' across fiber
-- var trace_n = 0; with Trace::mark = \-> { trace_n += 1 }
-- let _ = Fiber::spawn(mut s) \-> Trace::mark()       -- Error [E0615]: stateful handler cannot cross fiber boundary
```

- **`Sendable` (`E0301`)**: Admits value types, `.ril` shared objects without `ref`/`^mut` members whose constituents are `Sendable`, `Sender<U>` / `Receiver<U>`, and pure/stateless callables limited to `@io`, `@fiber`, and pure `fn` effects. Rejects `Scope`, `Task`, `Draft`, `use` bindings, and `.d.ril` `opaque` handles.
- **Cross-fiber isolation (`E0601`, `E0615`, `E0549`)**:
  - Every fiber capture must satisfy `Sendable` (`E0601` / `E0301`) and cannot capture `ref`, `mut`, `^mut`, `var`, `use` bindings (`E0601`), or stateful outer `fn` handlers (`E0615`).
  - Direct run-once closures (`run`, `spawn`, `zip`, `try_zip`, `race`, `supervise`, `timeout_ms`) may hand off `new`-qualified `Sendable` outer bindings once (`E0549` on reuse; contained sources must independently satisfy isolation).
- **Task-scope confinement (`E0604`)**: Each `scope` / `try_scope` creates a distinct confinement identity shared by its `Scope` and spawned `Task<T>` handles; neither may escape `body` or cross into another scope's `join`/`cancel` (`E0604`).
  - Normal `scope` exit awaits unjoined tasks in reverse spawn order; `try_scope` `Err` cancels and drains siblings.
- **`Result` inspection & supervision (`E0720`, `E0608`)**: `Task<!<T, E>>` must be `join`ed or `cancel`ed (`E0720`); `Receiver<!<T, E>>` requires `drain` (`close_recv` fails `E0720`); `zip`, `map`, `try_*`, `race`, `timeout_ms`, and `supervise` reject nested `!<U, E2>` payloads (`E0720`).
  - `supervise` enforces `E0608` panic isolation while permitting `@fiber` suspension and cancellation (yielding `TaskFault::Cancelled`).
- **Task & channel payloads (`E0548`, `E0535`)**:
  - `Channel::send` / `try_send` accept value copies or complete `new` `SharedObject` graphs free of existing-source boundaries (`E0548` on frozen snapshots, scoped `ref`/`mut`, or `new` wrappers over existing sources; pass `clone(...)`), so `recv` / `try_recv` return `new ?T` / `new !<T, TryRecvError>`.
  - `join(mut s, new task)` preserves `work`'s `infer T` qualification; plain/`ref` `join` freezes `T` (`E0535`).

```ril
-- File: ril/fiber.ril
pub opaque type Scope
pub opaque type Task<T |> Sendable>
pub type Zip<A, B, M1: MemberMode = let, M2: MemberMode = let> = .{ M1 first: A, M2 second: B }
pub type TaskFault { ..PanicError; Cancelled }
pub type TimeoutError { Elapsed }

pub fn run<T |> Sendable>(via action: fn() @& -> infer T) -> infer T
pub fn yield_now() @fiber -> ()
pub fn sleep_ms(ms: int) @io @fiber -> ()
pub fn is_cancelled() @fiber -> bool
pub fn uncancellable<T>(via action: fn() @& -> infer T) -> infer T
pub fn timeout_ms<T |> Sendable>(ms: int, via work: fn() @& -> infer T) @io @fiber -> infer !<T, TimeoutError>

pub fn scope<T>(via body: fn(mut Scope) @& -> infer T) @fiber -> infer T
pub fn try_scope<T, E>(
    via body: fn(mut Scope) @& -> infer !<T, E>,
) @fiber -> infer !<T, E>
pub fn supervise<T |> Sendable>(via work: fn() @& -> infer T) @fiber -> infer !<T, TaskFault>

pub fn spawn<T |> Sendable>(mut s: Scope, via work: fn() @& -> infer T) &mut -> new Task<T>
pub fn join<T |> Sendable>(mut s: Scope, via task: Task<T>) @fiber &mut -> infer T
pub fn cancel<T |> Sendable>(mut s: Scope, new task: Task<T>) @fiber &mut -> new ?T
pub fn cancel_scope(mut s: Scope) &mut -> ()

pub fn zip<A |> Sendable, B |> Sendable>(
    via left: fn() @& -> infer A,
    via right: fn() @& -> infer B,
) @fiber -> infer Zip<A, B>
pub fn try_zip<A |> Sendable, B |> Sendable, E |> Sendable>(
    via left: fn() @& -> infer !<A, E>,
    via right: fn() @& -> infer !<B, E>,
) @fiber -> infer !<Zip<A, B>, E>
pub fn map<T |> Sendable, U |> Sendable>(xs: []T, via work: fn(T) @ -> infer U) @fiber -> infer []U
pub fn try_map<T |> Sendable, U |> Sendable, E |> Sendable>(
    xs: []T,
    via work: fn(T) @ -> infer !<U, E>,
) @fiber -> infer !<[]U, E>
pub fn race<T |> Sendable>(via left: fn() @& -> infer T, via right: fn() @& -> infer T) @fiber -> infer T
```

```ril
-- File: ril/channel.ril
pub opaque type Sender<T |> Sendable> use(close)
pub opaque type Receiver<T |> Sendable>
pub type ChannelPair<T |> Sendable> = .{ mut tx: Sender<T>, mut rx: Receiver<T> }
pub type SendError<T> { Closed(T) }
pub type TrySendError<T> { Full(T); Closed(T) }
pub type TryRecvError { Empty; Closed }

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

---

## Compile-Time Computation and Introspection

### Static Type Values and Type Quotation

`Type<T>` is the exact static type of a compile-time **type value** representing type `T`. `<T>` quotes `T` into a static type value, and `<tv>` inside a type expression unquotes it back into a type:

```ril
type Nullable = \T = int -> <?T>
type Unpack = \T -> {
    let tv: Type<T> = <T>
    <.{ item: <tv> }>
}
type OptInt = Nullable<>
meta let _ = assert(<OptInt> == <?int> && <?int> == <Option<int>> && <!<int, str>> == <Result<int, str>>)
meta let _ = assert(<int> != <f64>)
-- let bad_bare = int                  -- Error [E0319]: bare type in value expression; write '<int>'
```

- **Quotation boundary (`E0319`)**: Bare `Type` in value annotations or bare type names in value expressions (`let x = int`) fail `E0319` (unit constructors such as `None`/`Disconnected` and callable constructors such as `Ok`/`UserId` are exempt).
- **Type-function parameters & defaults (`E0316`, `E0320`, `E0544`)**: Trailing defaults are supported (`E0316` if non-trailing; `E0320` on self/forward references). A `TypeDecl` whose RHS is a `TypeFunctionExpr` forbids `GenericParams` on `TypeDeclHead` (`E0120`), and a `ValueName` `TypeFnParam` omitting `: TypeExpression` requires a `|>` constraint (`E0544` otherwise).

```ebnf
TypeValueType    ::= "Type" "<" TypeExpression ">"
TypeFunctionExpr ::= "\" TypeFnParam { "," TypeFnParam } [ "," ] "->" Expression
TypeFnParam      ::= PascalCase [ TypeConstraint ] [ "=" TypeExpression ]
                   | ValueName [ ":" TypeExpression ] { "|>" PipelineConstraint } [ "=" Expression ]
                   | ModeParamDecl
```

### Pure Type Functions and Result Restrictions

Compile-time `type` functions, `meta fn`, and `meta let` run in a pure, deterministic static evaluator bounded by a compiler step budget:

```ril
meta fn align_up(n: int, align: int = 4096) -> int {
    assert(n >= 0 && align > 0)
    ((n + align - 1) / align) * align
}
meta let PAGE = align_up(3000)
meta let _ = assert(PAGE == 4096)
```

```ril
-- Rejected compile-time functions, values, and budget overflows:
-- meta let _ = assert(PAGE == 0)         -- Error [E0830]: static assertion failed
-- meta let _ = panic("boom")             -- Error [E0831]: static evaluation panicked
-- meta fn bad_tv() -> Type<int> { <int> } -- Error [E0812]: 'meta fn' cannot return 'Type<T>'
-- meta fn bad_io() @io -> int { 1 }      -- Error [E0813]: 'meta fn' must be pure
-- fn rt_tv(t: Type<int>) -> () {}        -- Error [E0816]: runtime parameter cannot hold 'Type<int>'
-- type Spin = \T -> Spin<T>
-- type Boom = Spin<int>                  -- Error [E0811]: compile-time evaluation budget exceeded
```

- **Pure Static Domain (`E0335`, `E0813`)**: `TypeFunctionExpr`, `meta fn`, and `meta let` permit local `var`/`let mut`, confined closures, loops, and recursion, while forbidding `@Eff` / `&State` annotations (`E0335` on type functions, `E0813` on `meta fn`).
- **Static Value & Storage Boundaries (`E0812`, `E0816`)**: `meta fn` returns and `meta(...)` attributes cannot expose `Type<T>` (`E0812`). `meta fn` returns, `meta let` constants, and `meta(...)` attributes cannot export callables or `use` resources, and runtime values, parameters, storage, and closures cannot hold `Type<T>` (`E0816`).
- **Compiler Root Evaluation Budget (`E0811`)**: Every compile-time root (`type` application, static check, `meta let`, `meta(...)`, static value argument, compile-time `meta fn` call) runs under a deterministic step budget (1 unit per call entry and loop iteration).
  - Exhausting the budget fails compilation with uncatchable `E0811` (partial type previews in diagnostics are informational only).
- **Static Defects (`E0830`, `E0831`)**: Failed static `assert` fails `E0830`; static `panic` or arithmetic defects fail `E0831`.

```ebnf
MetaLetDecl ::= [ Visibility ] "meta" "let" ( ScreamingSnakeCase | Wildcard ) [ ":" TypeExpression ] "=" Expression
MetaFnDecl  ::= { MetaAttr } [ Visibility ] "meta" "fn" ValueName [ GenericParams ]
                "(" [ ParameterList ] ")" ReturnSpec [ [ SignatureWhereClause ] Block ]
```

### Disjoint Call Families and Branch Pruning

```ril
use ril/platform

fn line_ending() -> str {
    if Platform::OS == "windows" { "\r\n" } else { "\n" } -- Statically unreachable branch eliminated after checking
}
fn describe<T>(x: T) -> str {
    match <T> {
        <int> -> "int:{x}"
        _     -> String::inspect(x)                       -- Resolved per concrete instantiation of T
    }
}
assert(describe(7) == "int:7" && describe(true) == "true")
```

| Evaluation context | Permitted calls (`E0810` otherwise) |
| :--- | :--- |
| `TypeEval` (type functions, static checks) | Type functions, `meta fn`, confined closures, static reflection, and dual-phase core ops (`len`, `inner`, `clone`, `derive`, `assert`, `panic`, `String::inspect`, plus pure `Array`/`Map`/`Set`/`String`/`Bytes`/`Numeric`) |
| `MetaValue` (`meta fn`, `meta let`, `meta(...)`) | `meta fn`, confined closures, static reflection, and dual-phase core operations |
| `RunTime` (`fn`, closures) | Ordinary `fn`, closures, foreign `.d.ril` `fn`, built-ins, plus direct saturated `meta fn` calls with static arguments (evaluated at compile time to immutable snapshots) |

- **`meta let` branch pruning**: In runtime functions, `if` / `match` branches over `meta let` constants (such as `Platform::OS`) are fully type-, mode-, and effect-checked on all branches; statically unreachable branches never execute, and `.d.ril` foreign symbols referenced solely within them must not be required to resolve in the target execution environment.
- **Generic `match <T>` resolution**: Static `match <T>` over an uninstantiated type parameter checks each arm under its static type fact and resolves to the single matching arm for each concrete instantiation of `T` (implementations may achieve this via specialization/monomorphization or any semantically equivalent mechanism).
- **Nonnegative static bounds (`E0815`)**: Negative static sizes or counts where nonnegative static values are required fail `E0815`.

### Static Introspection

```ril
type Select = \T: .{ .. }, keys: []str -> {
    let chosen = coords(<T>) |> Array::filter(\(_, k) -> Array::contains(keys, k))
    <.{ m [chosen as (m, k)]: T.(k) }>
}

type Model = .{ id: int, var title: str, mut rows: []int }
type Patch = Select<Model, ["title", "rows"]> -- .{ var title: str, mut rows: []int }
nominal type Args = .{ query: str, limit: int = 10 }
meta let _ = assert(Reflect::has_default(<Args>, "limit") && !Reflect::has_default(<Args>, "query"))
meta let _ = assert(len(coords(<Args>)) == 2 && coords(<(int, str)>)[0] == (MemberMode::Let, 0))

fn read_field<T: .{ .. }>(via rec: T, meta key: str |> Key<T>) -> infer T.(key) {
    rec.(key)
}
fn test_introspection() -> () {
    let m = Model.{ id: 9, title: "init", rows: [1] }
    assert(read_field(m, "title") == "init")
}
test_introspection()
```

```ril
-- Rejected introspection and mapped-record forms:
-- meta let _ = coords(<int>)            -- Error [E0358]: 'coords' requires a transparent record or tuple type
-- type BadMap = .{ [[1, 2] as k]: int } -- Error [E0341]: mapped record key must have type 'str'
-- type BadKey = .{ [["fn"] as k]: int } -- Error [E0815]: keyword 'fn' is not a valid FieldLabel
-- type BadIdx = (int, str).(-1)         -- Error [E0815]: negative static tuple coordinate '-1'
```

- **Constituent Projection (`T.(k)`)**: Projects field type `T.field` / `T.("field")` on accessible records (structural, `nominal`, in-scope `opaque`), `T.0` / `T.(0)` on tuples, and payload type `T.Variant` / `T.("Variant")` on transparent sums (`()` for unit variants; `E0308` on sealed `.ril` `opaque`, `E0907` on `.d.ril`).
- **`MemberMode` & `coords` / `variants`**:
  - Prelude `MemberMode` provides value constructors `MemberMode::Let`, `Var`, `Mut`, `SharedMut`, `Ref`, `VarMut`, `VarSharedMut`, and `VarRef` (corresponding to type-level `MemberModeLiteral` spellings `let`, `var`, `mut`, `^mut`, `ref`, `var mut`, `var ^mut`, `var ref`).
  - `coords(<T>) -> [](MemberMode, CoordKey<T>)` enumerates `(mode, field_name)` pairs in UTF-8 byte order for records (`CoordKey<T>` = `str`) and `(MemberMode::Let, index)` pairs in ascending index order for tuples (`CoordKey<T>` = `int`; `()` yields `[]`; `E0358` on other types, `E0308` when sealed).
  - `variants(<T>) -> []str` enumerates deduplicated variant names in UTF-8 byte order for closed transparent sums (`E0301` on non-sums; `E0308` when sealed or open `..`).
- **Mapped Record Types (`.{ [ModeModifier] [expr as pat]: Type }`)**: When `ModeModifier` is omitted or is a fixed `RecordFieldMode`, the comprehension iterable yields `str` keys directly (`E0341` otherwise); when `ModeModifier` is a `ValueName` bound by `pat`, the iterable yields `(MemberMode, str)` pairs whose first component supplies the mode and whose second component supplies the `str` key (`E0341` otherwise). Keys must be valid non-keyword `FieldLabel` syntax (`E0815`) with no duplicates (`E0210`). Value-type fields with `mut`/`^mut`/`ref` modes fail `E0402`; invalid mode values fail `E0356` / `E0357`.
- **Metadata Introspection (`Reflect`)**:
  - `Reflect::attrs<T, A>(target: Type<T>) -> []A`
  - `Reflect::field_attrs<T, A>(target: Type<T>, meta key: str |> Key<T>) -> []A`
  - `Reflect::variant_attrs<T, A>(target: Type<T>, meta variant: str) -> []A`
  - `Reflect::has_default<T>(target: Type<T>, meta key: str |> Key<T>) -> bool` (`true` iff `T` is a `nominal` or in-scope `opaque` record whose root field `key` declares `= expr`)

```ebnf
TypeProjection            ::= ( PrimaryType | TupleType | RecordType | TypeProjection ) "." ( FieldLabel | PascalCase | TupleIndex | "(" Expression ")" )
MappedRecordType          ::= ".{" [ ModeModifier ] MappedComprehensionClause ":" TypeExpression "}"
MappedComprehensionClause ::= "[" ForIterable "as" Pattern "]"
ModeModifier              ::= RecordFieldMode | ValueName
```

### Structural Type Pattern Matching

`let U` binds an exact type variable (or `MemberMode` in `let M field: ...`); bare `PascalCase` heads match concrete nominal, sum, or opaque type constructors (`E0306` on type-constructor pattern variables like `<(let F)<let X>>`):

```ril
type UnwrapResult = \T -> match <T> {
    <!<let OkT, _>> -> <OkT>
    <?let Inner>    -> <Inner>
    _               -> <T>
}
meta let _ = assert(<UnwrapResult<!<int, str>>> == <int>)
meta let _ = assert(<UnwrapResult<Result<int, str>>> == <int>)
meta let _ = assert(<UnwrapResult<?str>> == <str>)
```

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
TypePatternField      ::= [ MemberMode ] FieldLabel ":" TypePatternInner
                        | "let" PascalCase FieldLabel ":" TypePatternInner
TypeRestPattern       ::= ".." [ "let" PascalCase ]
TypePatternAccessMode ::= "mut" | "^mut" | "ref" | "let" PascalCase | StorageModeExpression
TypeArrayPattern      ::= "[" [ TypePatternAccessMode ] "]" TypePatternInner
TypeMapPattern        ::= "[" TypePatternInner ":" [ TypePatternAccessMode ] TypePatternInner "]"
RigidNominalPattern   ::= { "Super" "::" } { RigidPatternSegment "::" } RigidPatternSegment
RigidPatternSegment   ::= PascalCase [ "<" TypePatternArg { "," TypePatternArg } [ "," ] ">" ]
TypePatternArg        ::= TypePatternInner | "let" ValueName | MemberModeLiteral
PrimitivePattern      ::= PrimitiveType
```

---

## Modules, Program Execution, and Prelude

### Modules and Compilation Units

Ril enforces a **one-file-one-module** model with pure constant top-level initialization and non-generic isolated inline `sub` namespaces:

```ril
-- File: math/circle.ril
pub meta let PI = 3.141592653589793
pkg let internal_eps = 1.0e-9
type Hidden = .{ r: f64 }

pub fn area(r: f64) -> f64 { PI * r * r }             -- Zero '&up' needed for pure module constant 'PI'
pkg fn label_opaque(opaque: str) -> str { opaque }    -- 'pkg' is package visibility; 'opaque' is contextual

pub sub UnitCircle {
    pub opaque type Rad = f64
    pub fn zero() -> Rad { 0.0 }                      -- Bidirectional Rad <-> f64 inside 'UnitCircle'
    pub fn circumference() -> f64 { 2.0 * Super::PI } -- Isolated 'sub' reaches parent 'PI' via 'Super::'
}
```

```ril
-- Rejected module, sub-scope, and top-level purity forms:
-- sub UnitCircle { let _ = PI }                   -- Error [E0204]: 'PI' not in scope without 'Super::'
-- let _r: UnitCircle::Rad = 1.0                   -- Error [E0301]: expected 'UnitCircle::Rad', found 'f64'
-- let _k = coords(<UnitCircle::Rad>)              -- Error [E0308]: 'Rad' representation is sealed outside 'UnitCircle'
-- use Super::PI                                   -- Error [E0208]: file root has no enclosing 'Super'
-- pub fn leak() -> new Hidden { Hidden.{ r: 1.0 } } -- Error [E0910]: 'pub' signature leaks private 'Hidden'
-- var global_hits = 0                             -- Error [E0906]: top-level mutable state is prohibited
-- let boot_ts = Clock::now()                      -- Error [E0202]: top-level initializer must be pure
```

| Compilation unit / scope | Role & rules |
| :--- | :--- |
| **Executable Root (`.ril`)** | Non-`sub` entry file, unimportable (`E0208`); forbids root `pub`/`pkg` (`E0905`) and requires private root `fn main` (`E0903`, `E0904`) |
| **Library Module (`.ril`)** | Importable module named `to_pascal_case(file_stem)`; forbids `fn main` (`E0904`). Items default to file-private (`E0201`); files with zero root `pub` items have `pkg` visibility (`E0201` outside package) |
| **Foreign Interface (`.d.ril`)** | Bodyless foreign host declarations (`E0901` on bodies or `=` on `opaque type`); forbids `fn main` (`E0904`); nested `sub` blocks inherit `.d.ril` rules |

- **Inline `sub` (`[Visibility] sub Name`)**: Non-generic `PascalCase` namespace at file or `sub` top-level (`E0703` in statements, `E0702`/`E0704` in `where`, `E0203` on `sub Super`, `E0904` on `fn main`).
  - **Scope isolation**: Only the prelude is automatically in scope; `Super::` accesses enclosing file/`sub` items (`E0208` at file root); downward access requires `pub` or same-package `pkg` (`E0201`).
  - **Opaque boundary**: `opaque type` transparency stays strictly within its exact defining file or `sub` (`E0308`).
- **Top-Level Purity (`E0202`, `E0906`, `E0205`)**: File and `sub` top-level allow only pure deeply immutable `ValueName` `let` constants and `ScreamingSnakeCase` `meta let` constants (needing zero `&up` when read; `ScreamingSnakeCase` is exclusive to `meta let`, `E0101`).
  - Mutable, shared, live `ref`, or `use` top-level bindings (`var`, `let mut`, `let ^mut`, `let ref`, `use [mut] x = ...`) fail `E0906`; impure initializers fail `E0202`; top-level `?` fails `E0205`.

```ebnf
SourceFile ::= ModuleFile | DeclFile
ModuleFile ::= { ModuleItem Separator } [ ModuleItem ] EOF
DeclFile   ::= { DeclUnitItem Separator } [ DeclUnitItem ] EOF
ModuleItem ::= UseDecl | SubDecl | FunctionDecl | MetaFnDecl | MetaLetDecl
             | LetDecl | TypeDecl | NominalTypeDecl | OpaqueTypeDecl
             | SumTypeDecl | EffectDecl
SubDecl    ::= { MetaAttr } [ Visibility ] "sub" PascalCase "{" { SubItem Separator } [ SubItem ] "}"
SubItem    ::= ModuleItem
Visibility ::= "pub" | "pkg"
```

### Module Imports and Visibility

```ril
-- Context: math/circle.ril
use pkg/math/circle as Circle
use pkg/math/circle::(PI, area, UnitCircle as Uc)
```

```ril
-- Rejected imports and visibility leaks:
-- sub Helper { type Local = .{ x: int }; pub fn expose() -> new Local { Local.{ x: 1 } } } -- Error [E0910]: leaks private 'Local'
-- use pkg/math/missing                -- Error [E0208]: module 'pkg/math/missing' not found
-- use pkg/math/circle::nonexistent    -- Error [E0209]: 'nonexistent' not found in 'Circle'
-- let _ = Circle::Hidden.{ r: 1.0 }   -- Error [E0201]: 'Hidden' is private to 'Circle'
-- use pkg/net/a_b                     -- Error [E0102]: derived 'AB' violates PascalCase acronym rule
```

- **Package Roots (`E0208`, `E0209`)**: `pkg/...` resolves inside the current package, `ril/...` resolves standard-library modules, and `<dep>/...` resolves mounted dependencies (mount names `pkg` and `ril` are prohibited; missing modules or single-segment paths fail `E0208`; absent members fail `E0209`).
- **Default Module Binding (`E0102`, `E0203`)**: Unaliased `use pkg/http_server` binds `HttpServer` (`to_pascal_case("http_server")`), rejecting invalid acronym casings (`a_b` -> `AB`) and digit-leading segments (`sha_256`; write `sha256.ril` -> `Sha256`) with `E0102`, and rejecting `super.ril` with `E0203`.
- **Visibility Hierarchy (`E0201`)**: `private(scope) < pkg < pub`. Reachability along an inline `sub` path is capped by every enclosing `sub`, and `pub use` cannot widen target visibility (`E0201`).
- **Interface Consistency (`E0910`)**: Every type, non-opaque field/variant, `TypeFunctionExpr` body, parameter/field default, `use` cleanup function, and unhandled `@Eff` in a declaration must be accessible from every scope that can reach that declaration (`pub opaque` internal representations remain private).

```ebnf
UseDecl     ::= [ Visibility ] "use" FilePath [ "as" PascalCase ]
              | [ Visibility ] "use" ModulePath "::" ( "(" ImportList ")" | "*" | ImportItem )
PackageRoot ::= "pkg" | "ril" | SnakeCase
FilePath    ::= PackageRoot "/" SnakeCase { "/" SnakeCase }
ModulePath  ::= FilePath { "::" PascalCase }
              | "Super" { "::" "Super" } { "::" PascalCase }
              | PascalCase { "::" PascalCase }
ImportList  ::= ImportItem { "," ImportItem } [ "," ]
ImportItem  ::= Identifier [ "as" Identifier ]
```

### Program Entry Point

```ril
use ril/file
use ril/fiber

fn main() @io @fiber -> new !<(), str> {
    Fiber::yield_now()
    let raw = File::read("config.json")?
    if raw == "" { Err("empty config") } else { Ok() }
}
-- Missing 'fn main' in executable root       -- Error [E0903]
-- fn main(argc: int) -> int { argc }         -- Error [E0904]: invalid 'main' signature
-- sub Sub { fn main() -> () {} }             -- Error [E0904]: 'main' prohibited inside 'sub'
-- pub let root_export = 1                    -- Error [E0905]: 'pub' prohibited in executable root
```

- **Signature (`E0903`, `E0904`, `E0612`)**: `main` must be a non-public, non-generic ordinary `fn` at the executable root taking `()` and returning `()`, `!<(), str>`, or `new !<(), str>` (`E0903` if missing, `E0904` if malformed or inside `sub`). It may declare `@io` and `@fiber` (`E0612` on unhandled user-defined `eff`).
- **Exit status**: Returning `()` / `Ok()` exits `0`; returning `Err(msg)` prints `msg` + `\n` to stderr and exits `1`.

### Prelude Scope

The implicit prelude encloses every compilation unit and inline `sub`:
- **Types & effects**: Primitive types, `Option<T>` (`?T`; `Some(T); None`), `Result<T, E>` (`!<T, E>`; `Ok(T); Err(E)`), `Set<T>`, `PanicInfo`, `PanicError`, `MemberMode`, `Draft<T>`, `@io`, and `@fiber`.
- **Static checks & type helpers**: `SharedObject`, `Sendable`, `LenTarget`, `Tuple`, `NominalWrapper`, `Unwrap`, `CoordKey`, and `Key`.
- **Core modules**: `Array`, `Map`, `Set`, `String`, `Bytes`, `Numeric`, and `Reflect`.
- **Explicit standard imports**: `use ril/io`, `use ril/file`, `use ril/os`, `use ril/fiber`, `use ril/channel`, `use ril/platform`, `use ril/math`, and `use ril/crypto`.

#### Built-in Foundational Operations

| Built-in | Canonical signature | Phase & specification |
| :--- | :--- | :--- |
| `len` | `pub fn len<T \|> LenTarget>(via item: T) -> int` | Dual-phase: scalar count of `str`, byte count of `bytes`, element/entry count of `[]T`, `[K: V]`, `Set<T>` (admits `ref` on collections at runtime; `E0401` on `ref str`) |
| `inner` | `pub fn inner<W \|> NominalWrapper>(via wrapper: W) -> infer Unwrap<W>` | Dual-phase: unwraps accessible `.ril` `nominal` wrapper (or `Draft<W>`, lifting `NominalWrapper`/`Unwrap`) to its payload (`()` for unit nominals; `inner(mut x)` is a scoped path projection usable on `Draft<W>` or as an immediate `mut` path receiver, unable to bind a second unshared `let mut` alias, `E0510`; `E0907` on `.d.ril` nominals, `E0301` on non-nominals) |
| `clone` | `pub fn clone<T \|> SharedObject>(via value: T) -> new T` | Dual-phase: deep copy of clonable `SharedObject` graph into isolated `new T` (`E0301` on value types or graphs containing `.d.ril` `opaque` / concurrency / `Draft` handles; `E0530` on live/mutable closures) |
| `derive` | `pub fn derive<T \|> SharedObject>(base: T, via update: fn(mut Draft<T>) @& -> ()) -> T` | Dual-phase: path-targeted functional update on immutable `SharedObject` (`E0536`, `E0308`, `E0607`) |
| `absorb_panic` | `pub fn absorb_panic<T>(via action: fn() @& -> infer T) -> infer !<T, PanicError>` | Runtime: panic-isolated containment (`E0608`) |
| `panic_message` | `pub fn panic_message(info: PanicInfo) -> str` | Runtime: extracts human-readable message from `PanicInfo` (`E0810` in static eval) |
| `type_name` | `pub meta fn type_name<T>(tv: Type<T>) -> str` | Static only: diagnostic display string of `T` |
| `coords` | `pub meta fn coords<T>(tv: Type<T>) -> [](MemberMode, CoordKey<T>)` | Static only: `(mode, key)` pairs of accessible record (`str` keys) or tuple (`int` keys) `T` (`E0358` non-record/non-tuple, `E0308` sealed) |
| `variants` | `pub meta fn variants<T>(tv: Type<T>) -> []str` | Static only: variant tags of closed transparent sum `T` (`E0301` non-sum, `E0308` sealed/open) |
| `panic` | `pub fn panic(message: str) -> never` | Dual-phase: LIFO panic unwinding at runtime; `E0831` in static eval |
| `assert` | `pub fn assert(condition: bool, message: str = "assertion failed") -> ()` | Dual-phase: panics with `message` when `false` at runtime; `E0830` when `false` in static eval |
| `print` / `println` | `pub fn print(text: str) @io -> ()`<br>`pub fn println(text: str) @io -> ()` | Runtime (`@io`): writes UTF-8 text (plus `\n` for `println`) to stdout |

### Mandatory Inspection of Fallible Results

Every `!<T, E>` (`Result<T, E>`)—including `!<T, E>` parameters—must be inspected before normal scope exit (`E0720`):

```ril
fn write_entry(line: str) @io -> new !<(), str> {
    println(line)
    Ok()
}
fn handle_log() @io -> new !<(), str> {
    write_entry("propagated")?            -- OK: propagated via '?'
    write_entry("fallback") ?? \_e -> ()  -- OK: handled via '??'
    let r = write_entry("tested")
    assert(r == Ok())                     -- OK: reached comparison against 'Ok()' inspects Result
    let Ok() = write_entry("guarded") else { return Err("failed") }
    Ok()
}
```

```ril
-- Rejected uninspected Results (all fail E0720):
-- fn drop_any<T>(_x: T) -> () {}
-- write_entry("dropped")                 -- Error [E0720]: unused fallible Result
-- let _ = write_entry("ignored")         -- Error [E0720]: '_' does not inspect Result
-- drop_any(write_entry("generic"))       -- Error [E0720]: unconstrained generic parameter does not inspect Result
-- let _ = Some(write_entry("wrap"))      -- Error [E0720]: wrapped Result discarded uninspected
-- let a = write_entry("x"); let b = write_entry("y"); let _ = (a == b) -- Error [E0720]: non-constructor comparison
```

- **Satisfies inspection**: Testing the Result's constructor in a reached pattern (`match`, `if let`, `while let`, `let ... else`), comparing in a reached `==` / `!=` directly against `Ok(...)` or `Err(...)`, propagating (`?`), handling (`??`), passing to an explicitly `!<T, E>`-typed parameter, or returning.
- **Rejected (`E0720`)**: Discarding a `Result`, binding to `_`, passing to an unconstrained generic parameter `T`, wrapping in an uninspected composite value, comparing two non-constructor `Result` variables, or overwriting its last binding.

In a composite, each Result has its own obligation. Testing `Some(_)` examines the option tag. Testing `Some(Ok(_))` also examines the contained Result tag when the option is `Some`.

When a branch selects between existing Results or collections, inspection applies to the selected value on that branch. Traversing a collection to exhaustion discharges its element obligations when each visited Result is inspected, including Results in both halves of a map entry. A `break` leaves unvisited Results pending, and a `continue` preserves the obligation for any Result skipped in that iteration.

An early return through `?` exits normally with `Err` or `None`. An outstanding Result on that path must already have been inspected or be part of the returned value.

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
| **`E0210`** | [`DuplicateFieldError`](#record-types-and-open-record-tails) |
| **`E0212`** | [`OverlappingRowFieldError`](#record-types-and-open-record-tails) |
| **`E0213`** | [`ConflictingVariantSpreadError`](#sum-variant-spreading-and-subset-conversion) |

### Types, Expressions, Generics, and Patterns

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0301`** | [`TypeMismatchError`](#diagnostic-classification) |
| **`E0302`** | [`UnexpectedFieldError`](#record-types-and-open-record-tails) |
| **`E0303`** | [`NonExhaustiveMatchError`](#pattern-matching) |
| **`E0304`** | [`UnreachableMatchArmError`](#pattern-matching) |
| **`E0305`** | [`NominalTypeMismatchError`](#nominal-type-alias-and-opaque-types) |
| **`E0306`** | [`TypeKindMismatchError`](#generic-parameters-defaults-and-static-kinds) |
| **`E0307`** | [`MissingFieldError`](#record-types-and-open-record-tails) |
| **`E0308`** | [`OpaqueBoundaryViolationError`](#nominal-type-alias-and-opaque-types) |
| **`E0309`** | [`EmptyPatternBindingError`](#let-else-bindings) |
| **`E0310`** | [`InvalidatedNarrowingAccessError`](#flow-sensitive-type-narrowing) |
| **`E0311`** | [`ContradictoryNarrowingError`](#flow-sensitive-type-narrowing) |
| **`E0312`** | [`TupleIndexOutOfBoundsError`](#array-map-set-and-tuple-types) |
| **`E0313`** | [`CyclicTypeAliasError`](#type-equivalence-and-recursive-types) |
| **`E0314`** | [`ArityMismatchError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0315`** | [`EscapingLocalNominalTypeError`](#block-expressions-and-local-declarations) |
| **`E0316`** | [`NonTrailingDefaultGenericParamError`](#generic-parameters-defaults-and-static-kinds) |
| **`E0317`** | [`FunctionDefaultGenericProhibitedError`](#generic-parameters-defaults-and-static-kinds) |
| **`E0318`** | [`UntaggedUnionOrLiteralTypeError`](#generic-parameters-defaults-and-static-kinds) |
| **`E0319`** | [`BareTypeInExpressionContextError`](#static-type-values-and-type-quotation) |
| **`E0320`** | [`ForwardTypeDefaultReferenceError`](#generic-parameters-defaults-and-static-kinds) |
| **`E0321`** | [`NormallyCompletingElseError`](#let-else-bindings) |
| **`E0322`** | [`WildcardExpressionError`](#identifiers-and-casing-invariants) |
| **`E0323`** | [`InvalidStaticValueParamError`](#generic-parameters-defaults-and-static-kinds) |
| **`E0324`** | [`DynamicRecordIndexProhibitedError`](#record-types-and-open-record-tails) |
| **`E0325`** | [`DuplicateArgumentError`](#default-parameters-and-named-arguments) |
| **`E0326`** | [`LiteralOutOfRangeError`](#numeric-literals) |
| **`E0327`** | [`UnsupportedOperandTypeError`](#arithmetic-bitwise-relational-and-logical-operators) |
| **`E0328`** | [`InvalidCollectionKeyTypeError`](#arithmetic-bitwise-relational-and-logical-operators) |
| **`E0330`** | [`BareEffectTypeAliasError`](#type-definition-boundaries) |
| **`E0331`** | [`BareStateAnnotationTypeAliasError`](#type-definition-boundaries) |
| **`E0332`** | [`VariantEffectOrStateError`](#type-definition-boundaries) |
| **`E0333`** | [`FieldEffectOrStateError`](#type-definition-boundaries) |
| **`E0334`** | [`GenericEffectOrStateConstraintError`](#type-definition-boundaries) |
| **`E0335`** | [`TypeFunctionEffectOrStateError`](#type-definition-boundaries) |
| **`E0336`** | [`UnknownFieldError`](#record-types-and-open-record-tails) |
| **`E0337`** | [`InvalidMemberProjectionError`](#indexing-slicing-and-static-coordinate-projection); [Anonymous Functions, Trailing Closures, and Projection Accessors](#anonymous-functions-trailing-closures-and-projection-accessors) |
| **`E0338`** | [`NonCallableInvocationError`](#default-parameters-and-named-arguments) |
| **`E0339`** | [`UnknownNamedArgumentError`](#default-parameters-and-named-arguments) |
| **`E0340`** | [`GenericArityMismatchError`](#generic-parameters-defaults-and-static-kinds) |
| **`E0341`** | [`InvalidMappedRecordKeyTypeError`](#static-introspection) |
| **`E0344`** | [`InsufficientTypeInformationError`](#generic-parameters-defaults-and-static-kinds); [Anonymous Generalization and Fixed Storage](#anonymous-generalization-and-fixed-storage) |
| **`E0345`** | [`PartialPatternBindingError`](#let-else-bindings) |
| **`E0346`** | [`OrPatternBindingMismatchError`](#pattern-matching) |
| **`E0347`** | [`DuplicatePatternBindingError`](#pattern-matching) |
| **`E0348`** | [`InvalidRangePatternError`](#pattern-matching) |
| **`E0349`** | [`InvalidPatternExpressionError`](#pattern-matching) |
| **`E0350`** | [`NonBooleanConditionError`](#conditional-and-loop-expressions) |
| **`E0351`** | [`IncompatibleBranchTypesError`](#structural-joins-and-normal-completion) |
| **`E0352`** | [`InvalidIndexTargetError`](#indexing-slicing-and-static-coordinate-projection) |
| **`E0355`** | [`NonIterableValueError`](#conditional-and-loop-expressions) |
| **`E0356`** | [`InvalidMemberModeError`](#array-map-set-and-tuple-types) |
| **`E0357`** | [`IncompatibleMemberModeError`](#record-types-and-open-record-tails); [Member Modes and Implicit Schema Parameters](#member-modes-and-implicit-schema-parameters) |
| **`E0358`** | [`InvalidCoordsTargetError`](#static-introspection) |
| **`E0359`** | [`InvalidFieldDefaultPlacementError`](#record-types-and-open-record-tails) |
| **`E0360`** | [`UnfinishedExpressionHoleError`](#expression-grammar-and-precedence) |
| **`E0361`** | [`DivisionOrShiftDomainError`](#arithmetic-bitwise-relational-and-logical-operators) |

### Parameters, Argument Modes, and Defaults

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0401`** | [`ValueTypeReferenceParameterError`](#value-types) |
| **`E0402`** | [`ValueTypeReferenceModeError`](#value-types) |
| **`E0403`** | [`VarParameterProhibitedError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0404`** | [`MutableParameterDefaultProhibitedError`](#default-parameters-and-named-arguments); [Record Types and Open Record Tails](#record-types-and-open-record-tails) |
| **`E0405`** | [`MissingArgumentModeMarkerError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0406`** | [`InvalidArgumentModeError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0407`** | [`CallableParameterModeMismatchError`](#callable-compatibility) |
| **`E0408`** | [`InvalidDefaultParameterReferenceError`](#default-parameters-and-named-arguments); [Record Types and Open Record Tails](#record-types-and-open-record-tails) |
| **`E0409`** | [`ImpureParameterDefaultError`](#default-parameters-and-named-arguments); [Signature Guards](#signature-guards); [Record Types and Open Record Tails](#record-types-and-open-record-tails) |
| **`E0410`** | [`InvalidMutableArgumentTargetError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0411`** | [`InvalidNewParameterError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0412`** | [`InvalidModeInferencePlacementError`](#access-mode-inference-with-via-and-infer) |

### Bindings, State, Access Modes, and Scoped Resources

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0501`** | [`ImmutableReassignmentError`](#binding-modes-and-storage-matrix) |
| **`E0502`** | [`PinnedBindingReassignmentError`](#binding-modes-and-storage-matrix) |
| **`E0503`** | [`InvalidAssignmentTargetError`](#record-construction-and-assignments) |
| **`E0510`** | [`MissingStateAnnotationError`](#mandatory-signature-inference-and-completion) |
| **`E0520`** | [`UnauthorizedMutationError`](#exclusivity-and-authority-escalation-matrix) |
| **`E0521`** | [`InvalidPatternMutableBindingError`](#exclusivity-and-authority-escalation-matrix) |
| **`E0522`** | [`InvalidContainerElementModeError`](#exclusivity-and-authority-escalation-matrix) |
| **`E0523`** | [`MutMutAliasingConflictError`](#exclusivity-and-authority-escalation-matrix) |
| **`E0524`** | [`ReadMutAliasingHazardError`](#exclusivity-and-authority-escalation-matrix) |
| **`E0526`** | [`CollectionMutationDuringIterationError`](#exclusivity-and-authority-escalation-matrix) |
| **`E0527`** | [`UnusedAuthorityError`](#reachable-authority-use) |
| **`E0528`** | [`InvalidReturnAuthorityError`](#exclusivity-and-authority-escalation-matrix) |
| **`E0529`** | [`ExcessiveStateAnnotationError`](#local-state-containment-parameter-mutation-and-sharing) |
| **`E0530`** | [`IllegalNonClonableAuthorityError`](#deep-immutability) |
| **`E0531`** | [`InvalidRefSourceError`](#subtyping-reception-and-callable-compatibility) |
| **`E0532`** | [`ReassignableScopedResourceError`](#scoped-resource-bindings); [Foreign Interface Declarations](#foreign-interface-declarations) |
| **`E0533`** | [`AliasedNarrowingHazardError`](#flow-sensitive-type-narrowing) |
| **`E0534`** | [`CallableSignatureMismatchError`](#callable-compatibility) |
| **`E0535`** | [`CannotFreezeValueError`](#deep-immutability) |
| **`E0536`** | [`InvalidDeriveInputError`](#functional-updates-via-derive) |
| **`E0537`** | [`LiveCollectionInvalidationError`](#indexing-slicing-and-static-coordinate-projection) |
| **`E0538`** | [`InvalidStateClauseError`](#state-groups-and-captured-layers) |
| **`E0541`** | [`InvalidScopedCleanupError`](#scoped-resource-bindings) |
| **`E0543`** | [`UnanchoredRefSourceError`](#subtyping-reception-and-callable-compatibility) |
| **`E0544`** | [`MissingInferredFunctionAnnotationError`](#mandatory-signature-inference-and-completion); [Signature Guards](#signature-guards) |
| **`E0545`** | [`InvalidReturnSourceError`](#return-construction-access-modes-and-sources) |
| **`E0546`** | [`InvalidNewReturnError`](#return-construction-access-modes-and-sources) |
| **`E0547`** | [`InvalidOpenEffectOrStatePlacementError`](#closed-and-open-effect-and-state-sets) |
| **`E0548`** | [`InvalidNewSourceError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0549`** | [`UseAfterNewHandoffError`](#new-qualified-locals-and-mode-preserving-reception) |
| **`E0550`** | [`RedundantModeViaError`](#inference-domains-and-signature-completion) |
| **`E0551`** | [`InvalidPatternDecompositionError`](#pattern-matching) |
| **`E0552`** | [`IncompatibleInferredInterfaceError`](#inferred-interfaces-and-callable-families) |

### Effects, Concurrency, and Escape

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0601`** | [`CrossFiberCaptureError`](#structured-fiber-concurrency-and-channels) |
| **`E0604`** | [`ScopedValueEscapeError`](#scoped-resource-bindings); [Structured Fiber Concurrency and Channels](#structured-fiber-concurrency-and-channels) |
| **`E0607`** | [`DeriveDraftEscapeError`](#functional-updates-via-derive) |
| **`E0608`** | [`PanicIsolationViolationError`](#panic-absorption-with-absorb_panic) |
| **`E0612`** | [`UnhandledEffectError`](#effect-declarations-and-handlers) |
| **`E0613`** | [`ValueEffectAnnotationError`](#type-definition-boundaries) |
| **`E0615`** | [`CrossFiberStatefulHandlerError`](#structured-fiber-concurrency-and-channels) |
| **`E0616`** | [`ScopedCleanupEffectError`](#scoped-resource-bindings) |
| **`E0618`** | [`UnhandledLocalEffectError`](#block-expressions-and-local-declarations) |
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
| **`E0712`** | [`InvalidPropagationOperandError`](#pipeline-and-fallible-operators); [Signature Guards](#signature-guards) |
| **`E0713`** | [`IncompatiblePropagationTargetError`](#pipeline-and-fallible-operators); [Signature Guards](#signature-guards) |
| **`E0714`** | [`InvalidFallbackOperandError`](#pipeline-and-fallible-operators) |
| **`E0715`** | [`InvalidSafeAccessReceiverError`](#pipeline-and-fallible-operators) |
| **`E0720`** | [`UnusedFallibleResultError`](#mandatory-inspection-of-fallible-results) |

### Static Computation

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0810`** | [`CallFamilyViolationError`](#disjoint-call-families-and-branch-pruning) |
| **`E0811`** | [`CompileTimeBudgetExceededError`](#pure-type-functions-and-result-restrictions) |
| **`E0812`** | [`TypeValueReturnProhibitedError`](#pure-type-functions-and-result-restrictions) |
| **`E0813`** | [`ImpureMetaFnError`](#pure-type-functions-and-result-restrictions) |
| **`E0814`** | [`StaticValueRequiredError`](#generic-parameters-defaults-and-static-kinds) |
| **`E0815`** | [`InvalidStaticValueError`](#disjoint-call-families-and-branch-pruning) |
| **`E0816`** | [`RuntimeTypeValueProhibitedError`](#pure-type-functions-and-result-restrictions) |
| **`E0830`** | [`StaticAssertionFailedError`](#pure-type-functions-and-result-restrictions) |
| **`E0831`** | [`StaticEvaluationPanicError`](#pure-type-functions-and-result-restrictions) |

### Module Forms, Entry Points, and Foreign Interfaces

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0901`** | [`BodyInForeignInterfaceError`](#foreign-interface-declarations) |
| **`E0902`** | [`MissingDeclarationBodyError`](#foreign-interface-declarations) |
| **`E0903`** | [`MissingEntryPointError`](#program-entry-point) |
| **`E0904`** | [`InvalidEntryPointError`](#program-entry-point) |
| **`E0905`** | [`RootUnitExportProhibitedError`](#modules-and-compilation-units) |
| **`E0906`** | [`TopLevelMutableStateProhibitedError`](#modules-and-compilation-units) |
| **`E0907`** | [`ForeignRepresentationAccessError`](#foreign-interface-declarations) |
| **`E0908`** | [`UnsupportedForeignAuthorityError`](#foreign-interface-declarations) |
| **`E0909`** | [`BuiltinSignatureMismatchError`](#named-function-declarations-and-contrast-matrix) |
| **`E0910`** | [`ExportedVisibilityLeakError`](#module-imports-and-visibility) |
