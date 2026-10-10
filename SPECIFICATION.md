# The Ril Language Specification

**Version:** 0.1.0  
**Status:** Canonical Reference Specification  
**Format:** Code-First Normative Document  

---

## 1. Notation, Abstract Machine & Conformance

### 1.1 Notation

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
let y: str = 42                        -- Error [E0301]: type mismatch, expected str, found int
let z = 10 / 0                         -- Panics: division by zero
```

### 1.2 Conformance

A conforming Ril implementation MUST:
1. Accept all syntactically and semantically valid Ril programs defined herein.
2. Statically reject all invalid programs with the exact diagnostic conditions specified herein.
3. Emit artifacts adhering strictly to the abstract machine semantics, memory model, and determinism invariants.

### 1.3 Abstract Machine & Memory Semantics

Ril executes on an abstract machine with automatic memory management (tracing garbage collection). Evaluation order is strictly left-to-right. Numeric operations on fixed-width types are strictly deterministic across all target architectures.

```ril
-- Strict left-to-right evaluation order across operands and arguments:
let mut trace: []int = []
let log = \n -> { trace !> Array::push(n); n }
let result = log(1) + log(2) * log(3)  -- Evaluates log(1), then log(2), then log(3)
-- trace is guaranteed to be [1, 2, 3]
```

### 1.4 Failure Model & Error Categories

Ril enforces a strict separation between domain recoverable errors and program defects:

1. **Recoverable Errors**: Represented as ordinary sum type values (`Result<T, E>` and `Option<T>` / `?T`). Unused `Result` values are statically rejected.
2. **Defects (Panics)**: Invariant violations (division by zero, out-of-bounds indexing, failed `assert`, integer overflow) raise **Deterministic Runtime Panics**.
3. **Synchronous Isolation**: Panics cannot be caught within synchronous evaluation frames.
4. **Boundary Containment**: In concurrent execution, child task panics are isolated at structured concurrency boundaries (`scope`), resolving to `Result<T, TaskFault>` (`TaskFault::Panicked`).

```ril
-- 1. Recoverable error handling via Result and '?':
fn parse_id(s: str) -> Result<int, str> {
    if s == "" { Err("empty input") } else { Ok(42) }
}
let id = parse_id("10")?               -- OK: propagated via postfix '?'
-- parse_id("10")                       -- Error [E0720]: unused fallible Result must be handled

-- 2. Deterministic runtime panic on defect:
let arr = [1, 2, 3]
let item = arr[5]                      -- Panics: index out of bounds (index 5, length 3)
let safe_item = arr?[5]                -- OK: safe index evaluates to Option<int> (None)

-- 3. Synchronous Isolation: panics cannot be caught synchronously
fn faulty_frame() -> int {
    let _ = 10 / 0                     -- Panics: division by zero; aborts current stack frame immediately
    100                                -- Unreachable
}

-- 4. Boundary Containment: child panics isolated at structured scope boundary
use ril/concurrent::{scope, TaskFault}

let scope_outcome: Result<int, TaskFault> = scope(\mut s -> {
    s.fork(\-> { panic("worker failure") })
    Ok(42)
})
-- scope_outcome evaluates to Err(TaskFault::Panicked(...))
```

---

## 2. Source Text & Lexical Elements

### 2.1 Character Set & Encoding

Source text is encoded in UTF-8. Case is significant.

### 2.2 Comments

```ebnf
LineComment  ::= "--" { SourceChar } ( Newline | EOF )
BlockComment ::= "{-" { SourceChar | BlockComment } "-}"
```

```ril
-- Single-line comment to end of line
{- Block comment {- nested block comment -} continues -}
```

### 2.3 Whitespace & Layout Rules

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

### 2.4 Identifiers & Casing Invariants

```ebnf
Identifier         ::= PascalCase | SnakeCase | ScreamingSnakeCase | SuppressedVar
PascalCase         ::= [A-Z] { [a-zA-Z0-9] }
SnakeCase          ::= [a-z] [a-z0-9]* { "_" [a-z0-9]+ }
ScreamingSnakeCase ::= [A-Z] [A-Z0-9]* { "_" [A-Z0-9]+ }
SuppressedVar      ::= "_" [a-z] [a-z0-9]* { "_" [a-z0-9]+ }
Wildcard           ::= "_"
```

Identifiers are strictly partitioned at the lexer and parser levels across grammatical roles under the **Closed Casing Invariant**:

1. **`PascalCase`**: Strictly reserved for types (`type`), ADT variant constructors, nominal wrappers, algebraic effects (`eff`), and generic type parameters (`T`, `ItemType`).
   - **Acronym Title-Casing Rule**: Acronyms within `PascalCase` MUST be title-cased as regular words (`HttpServer`, `UserId`, `JsonParser`, NOT `HTTPServer`, `UserID`, `JSONParser`) (`E0102`).
2. **`snake_case`**: Strictly used for runtime variables (local bindings, function parameters, reassignable variables `var`, and pinned mutable handles `let mut`), const generic parameters (`cap: int`), named functions (`fn`, `meta fn`), record fields, and module path segments.
3. **`SCREAMING_SNAKE_CASE`**: Strictly reserved for compile-time constants (`meta let`) and top-level immutable constants (`let`). Top-level mutable variables (`var`, `let mut`) MUST use `snake_case`.
4. **Wildcard & Suppression**: A single underscore `_` is strictly the wildcard discard pattern, not an identifier (`E0301`). An identifier with a leading underscore `_snake_case` declares an intentionally unused variable or parameter, suppressing unused binding diagnostics (`E0527`).

```ril
-- 1. PascalCase: Types, Constructors, Effects, and Generic Parameters
type UserAccount = { id: int }         -- OK: type identifier
type Result<T, E = str> { Ok(T), Err(E) } -- OK: generic parameters and constructors
eff FileIo { read() -> str }           -- OK: effect identifier
type HttpServerConfig = { port: int }  -- OK: title-cased acronym

-- 2. snake_case: Variables (local, param, top-level var / let mut), Functions, and Fields
let user_count = 10                    -- OK: local variable identifier
var total_score = 0                    -- OK: local reassignable variable
var active_workers = 0                 -- OK: top-level reassignable mutable variable
fn compute_area(width: f64) -> f64 { width * 2.0 } -- OK: function identifier
meta fn pad_align(size: int) -> int { size }       -- OK: compile-time function

-- 3. SCREAMING_SNAKE_CASE: meta let and Top-Level Immutable Variables ONLY
meta let MAX_BUFFER_SIZE = 1024 * 64   -- OK: compile-time constant
let DEFAULT_TIMEOUT_MS = 5000          -- OK: top-level immutable constant

-- 4. Wildcard and Unused Suppression
let _ = user_count                     -- OK: wildcard discard
fn on_event(ev: Event, _ctx: Context) { handle(ev) } -- OK: '_ctx' suppresses unused warning

-- Static Lexical Violations:
-- type user_doc = { id: int }         -- Error [E0101]: type identifier must be PascalCase, found 'user_doc'
-- fn Calculate() -> () {}             -- Error [E0101]: function identifier must be snake_case, found 'Calculate'
-- let UserCount = 10                  -- Error [E0101]: variable identifier must be snake_case, found 'UserCount'
-- meta let max_size = 100             -- Error [E0101]: compile-time constant must be SCREAMING_SNAKE_CASE, found 'max_size'
-- var ACTIVE_FLAG = true              -- Error [E0101]: top-level mutable variable must be snake_case, found 'ACTIVE_FLAG'
-- type HTTPServer = { port: int }     -- Error [E0102]: acronym in PascalCase must be title-cased, expected 'HttpServer'
-- let user__name = "Alice"            -- Error [E0102]: consecutive underscores are prohibited, found 'user__name'
-- let Some(USER_ID) = opt             -- Error [E0103]: pattern binding position cannot use uppercase identifier
-- let _ = 10; println(_)              -- Error [E0301]: wildcard '_' cannot be evaluated as an expression
```

### 2.5 Keywords

The following 36 tokens are strictly reserved keywords:

```
as       eff      else     false    fn
for      halt     if       in       infer
is       keyof    last     let      loop
match    meta     module   mut      never
next     opaque   pub      resume   return
scoped   test     true     type     typeof
use      var      view     where    while
with
```

```ril
-- Reserved keywords in action:
pub opaque type Token = int            -- 'pub', 'opaque', 'type'
meta let COMPILE_ID = 101              -- 'meta', 'let'
eff Logger { log(str) -> () }          -- 'eff'
use ril/array::{push}                  -- 'use'
halt fn total_step() -> bool { true }  -- 'halt', 'true', 'fn'
let scoped res = File::open("a.txt")?  -- 'scoped' in let binding
let view v = res                       -- 'view' in handle binding
with Logger::log(msg) -> resume ()     -- 'with', 'resume' (statement-level handler)

fn calculate(val: ?int) -> int {       -- 'fn'
    let bound = match val {            -- 'let', 'match'
        Some(x) if x > 0 -> x,         -- 'if'
        _ -> 0,
    }
    let is_positive = bound is 1..=10  -- 'is'
    var sum = 0                        -- 'var'
    for n in [1, 2, 3] {               -- 'for', 'in'
        if sum > 10 { last }           -- 'last'
        else { next }                  -- 'else', 'next'
    }
    while false { loop {} }            -- 'while', 'false', 'loop'
    bound                              -- tail expression
where                                  -- 'where' inside block
    type Dummy = never                 -- 'never'
}
```

### 2.6 Numeric Literals

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

### 2.7 Text & Byte Literals

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

### 2.8 Boolean & Unit Literals

```ril
let is_valid = true                    -- Type: bool
let is_done = false                    -- Type: bool
let unit_val = ()                      -- Type: ()
```

---

## 3. Types & Memory Model

### 3.1 Value Types

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

-- let mut bad_scalar = a              -- Error [E0402]: value type 'int' has no interior mutability; use 'var'
-- fn bad_borrow(mut x: int) {}        -- Error [E0401]: value types cannot be borrowed as 'mut' parameters
```

### 3.2 Reference Types

Reference types are allocated on the managed garbage-collected heap: records, arrays, tuples, maps, sets, and sum type instances.

```ril
-- Reference types: shared heap aliasing:
type Node = { mut val: int }
let mut n1 = Node.{ val: 10 }
let view n2 = n1                       -- 'n2' aliases the exact same heap record as a live view
n1.val = 99                            -- Mutate through 'n1'
assert(n2.val == 99)                   -- OK: 'n2' observes mutation due to reference aliasing

-- Mutating through read-only alias is strictly prohibited:
-- n2.val = 100                        -- Error [E0520]: cannot mutate through read-only view 'n2'
```

### 3.3 Record Types & Row Polymorphism

Records are structural collections of named fields. Closed records do not support width subtyping. Field access on records is strictly compile-time identifier dot-access (`r.field`); dynamic string indexing (e.g. `r["key"]` or `r.("key")`) is prohibited. In symmetry, type-level field extraction uses dot projection (`User.id` or computed projection `T.(K)`); bracket indexing on record types (e.g. `User["id"]`) is prohibited (`E0301`).

Named row tail polymorphism (`..R`) allows generic functions to accept and preserve additional caller fields across pipelines. Pattern destructuring with `..rest` extracts a concrete, statically typed sub-record containing the remaining known fields.

```ebnf
RecordType     ::= "{" [ RecordField { "," RecordField } [ "," ] [ ".." Identifier ] ] "}"
RecordField    ::= [ "mut" ] Identifier ":" TypeExpression
TypeProjection ::= PrimaryType "." ( Identifier | IntLiteral | "(" TypeExpression ")" )
```

```ril
type User = { id: int, name: str }
let u: User = .{ id: 1, name: "Alice" } -- OK: exact closed record match

-- 1. Closed record rejects unexpected fields (E0302):
-- let bad_u: User = .{ id: 1, name: "Alice", age: 30 } -- Error [E0302]: unexpected field 'age' in closed record 'User'

-- 2. Field access is strictly compile-time identifier dot-access:
let user_id = u.id                     -- OK: direct static offset lookup
-- let bad_index = u["name"]           -- Error [E0301]: records do not support dynamic index lookup
-- let bad_accessor = u.("name")       -- Error [E0301]: dynamic string accessor prohibited

-- 3. Type-level field projection:
type IdType = User.id                  -- OK: direct static field type extraction (int)
-- type BadIndex = User["id"]          -- Error [E0301]: record types do not support bracket indexing, use User.id

-- 4. Named row tail polymorphism (generic type preservation):
fn with_timestamp<R>(r: { ..R }) -> { timestamp: int, ..R } {
    .{ timestamp: 1600000000, ..r }
}
let stamped = with_timestamp(.{ id: 1, tag: "audit" })
assert(stamped.tag == "audit" && stamped.timestamp == 1600000000)

-- 5. Type-precise rest destructuring:
type Account = { id: int, username: str, email: str, role: str }
let acc: Account = .{ id: 42, username: "admin", email: "adm@ril.org", role: "root" }

let .{ id, ..rest } = acc
-- 'rest' has static inferred type: { username: str, email: str, role: str }
assert(rest.username == "admin")
assert(rest.email == "adm@ril.org")
assert(rest.role == "root")
```

### 3.4 Array, Map, Set & Tuple Types

Bracket syntax (`[...]`) unifies all runtime dynamic collections: linear sequences (`[]T`), associative maps (`[K: V]`), and sets (`Set<T>`). Fixed-arity anonymous products are represented as tuples (`(T1, T2)`).

```ebnf
ArrayType   ::= "[]" TypeExpression
MapType     ::= "[" TypeExpression ":" TypeExpression "]"
SetType     ::= "Set" "<" TypeExpression ">"
TupleType   ::= "(" TypeExpression "," { TypeExpression "," } [ TypeExpression ] ")"
```

```ril
-- 1. Linear Array ([]T):
let numbers: []int = [1, 2, 3]         -- Type: []int

-- 2. Associative Map ([K: V]):
let config: [str: str] = ["env": "prod", "host": "127.0.0.1"]
let empty_map: [str: int] = [:]        -- Empty map literal
let host = config["host"]              -- Evaluates to ?str (Some("127.0.0.1"))

-- 3. Unique Set (Set<T>):
let visited: Set<int> = [10, 20, 30]    -- Contextual initialization from collection literal
let roles = Set.["admin", "guest"]     -- Explicit Set.[...] constructor literal

-- 4. Tuple ((T1, T2)):
let coords: (int, str) = (10, "Alice") -- Type: (int, str)
let x = coords.0                       -- Value positional access: 10
let name = coords.1                    -- Value positional access: "Alice"
type CoordX = (typeof coords).0        -- Inferred tuple positional projection: int
type First = (int, str).0              -- Static tuple positional projection: int
-- type OutOfBounds = (int, str).2      -- Error [E0301]: tuple index 2 out of bounds for (int, str)

-- 5. Collection Type Parameter Extraction (modular, non-prelude):
use ril/array::{Elem}
use ril/map::{Key, Value}

type IntElem = Elem<[]int>             -- Resolves to int
type HostKey = Key<[str: int]>         -- Resolves to str
type PortVal = Value<[str: int]>       -- Resolves to int

-- Collections are not product types; dot projection on collections is rejected:
-- type BadArrElem = ([]int).elem      -- Error [E0301]: collections do not have named fields; use ril/array::{Elem}
-- type BadMapKey = ([str: int]).key   -- Error [E0301]: collections do not have named fields; use ril/map::{Key}
```

### 3.5 Sum Types & GADTs

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
        -- LitBool(b) -> 0             -- Error [E0301]: unreachable match arm: constructor 'LitBool' binds T = bool, incompatible with Expr<int>
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

Because Ril strictly possesses no 1-element tuples `(T,)` (`(x)` denotes parenthesized grouping; tuples require $\ge 2$ elements; `()` denotes unit), constructor arity $n$ in expressions and patterns is strictly deterministic:
1. **Scope Restriction (Strict Constructor Boundary)**: Equivalence is confined strictly to Data Constructors. Ordinary functions (`fn`), closures, and methods maintain strictly separate parameter lists and register ABIs (`E0301`).
2. **Positional Tuple Expansion ($n \ge 2$)**: In expression construction and pattern matching, $C(e_1, \dots, e_n)$ constructs or matches the tuple payload elements directly. Outer constructor parentheses absorb inner tuple parentheses.
3. **Whole-Tuple Binding or Single Argument ($n = 1$)**: $C(val)$ constructs or matches the scalar payload or whole-tuple object.
4. **Unit Payload Constructor ($n = 0$)**: When a variant's payload type is `()`, $C()$ constructs or matches the unit payload directly ($C() \equiv C(())$). Bare constructor identifiers without parentheses (e.g. bare `Ok`) are strictly first-class constructor functions (`fn(T) -> Result<T, E>`), and cannot be evaluated as values without `()` (`E0301`).
5. **Nullary Variant Tag Invariant**: Variants declared without a payload (e.g. `None` in `type Option<T> { Some(T), None }`) are pure zero-field tags: they MUST be written without parentheses (`None`). Supplying argument parentheses to a nullary variant (`None()`) is statically rejected (`E0301`).
6. **Explicit Tuple Literal Compatibility**: Explicit tuple literals $C((e_1, \dots, e_n))$ and patterns $C((p_1, \dots, p_n))$ remain valid as supplying a 1-argument tuple payload directly.
7. **Non-Transitivity (Single-Layer Invariant)**: Equivalence applies strictly to the outermost constructor argument boundary. Nested tuples (e.g. `Variant((A, B), C)`) require explicit grouping and do NOT flatten recursively (`Variant(a, b, c)` is rejected with `E0301`).
8. **Rigid Type Variable Invariant**: Deconstructing $C(p_1, \dots, p_n)$ ($n \ge 2$) against an unconstrained generic type parameter $T$ is statically rejected with `E0301`.
9. **First-Class Constructor Canonical Type**: A constructor $C$ carrying a tuple payload $(T_1, \dots, T_n)$ possesses the canonical unary first-class callable type $\text{fn}((T_1, \dots, T_n)) \to S$. In Check Mode expecting a multi-parameter callable ($\Gamma \vdash C \Leftarrow \text{fn}(T_1, \dots, T_n) \to S$), the compiler applies context-directed $\eta$-expansion ($\backslash x_1, \dots, x_n \to C(x_1, \dots, x_n)$).

```ril
-- 1. Result construction and matching with unit payload (n = 0):
let unit_res: Result<(), str> = Ok()             -- OK: n = 0 constructs () payload directly
let auto_unit = Ok()                             -- OK: synthesizes Result<(), _> (payload is ())
-- let bad_bare = Ok                             -- Error [E0301]: 'Ok' is a constructor function; write 'Ok()' to construct Result<(), _>

match unit_res {
    Ok() -> println("success"),                  -- OK: n = 0 matches () unit payload
    Err(e) -> println(e),
}

-- 2. Nullary variant tags vs. Data constructors:
let opt: Option<int> = None                      -- OK: nullary tag without parentheses
-- let bad_none = None()                         -- Error [E0301]: variant 'None' has no payload; remove parentheses

-- 3. Result construction and matching with tuple payload:
let res: Result<(int, str), str> = Ok(200, "OK") -- OK: n = 2 constructs (int, str) directly
let pair = (200, "OK")
let res_from_pair = Ok(pair)                     -- OK: n = 1 passes existing tuple
let res_compat = Ok((200, "OK"))                 -- OK: n = 1 explicit tuple literal

match res {
    Ok(code, msg) -> println(msg),               -- OK: n = 2 directly unpacks tuple elements
    Ok(p) -> println(p.1),                       -- OK: n = 1 binds entire tuple to 'p'
    Err(e) -> println(e),
}

-- 4. Multi-field variant declaration and tuple equivalence:
type Geometry {
    TwoPoints(int, int),                         -- Equivalent to TwoPoints((int, int))
}

let p1 = TwoPoints(10, 20)                       -- OK: positional elements
let p2 = TwoPoints(pair)                         -- OK: passing existing tuple variable
let TwoPoints(x, y) = p1                         -- OK: positional destructuring
let TwoPoints(raw_tuple) = p1                    -- OK: whole-tuple destructuring

-- 5. Functions do NOT auto-tuple (Strict Scope Boundary):
fn add(a: int, b: int) -> int { a + b }
let sum1 = add(1, 2)                             -- OK: 2 arguments
-- let sum2 = add(pair)                          -- Error [E0301]: expected 2 arguments, found 1 tuple

-- 6. Nested tuples: non-transitive boundary:
type Node {
    Branch((int, int), str),                     -- Payload is 2-tuple: ((int, int), str)
}
let node = Branch((1, 2), "left")                -- OK: n = 2 arguments
-- let bad_node = Branch(1, 2, "left")           -- Error [E0301]: arity mismatch: expected 2 arguments, found 3
```

### 3.6 Nominal Type Wrappers

Nominal wrappers encapsulate an underlying type into an isolated nominal identity with zero runtime overhead.

```ebnf
NominalDecl ::= [ "pub" ] "type" Identifier [ GenericParams ] [ "(" TypeExpression ")" ] [ WhereClause ]
```

When `(TypeExpression)` is omitted, `NominalDecl` defines a **Unit Nominal Type** (e.g. `type Marker`).
- **Memory Layout**: Unit nominal types have a 0-byte memory layout (zero-sized type / ZST) and compile to zero runtime overhead.
- **Value Construction**: The bare identifier `Marker` denotes its canonical singleton value (`let m = Marker`).
- **Pattern Matching**: `Marker` acts as a nullary constructor pattern in multi-variant `match` expressions (`match event { Marker -> ... }`). In `let` statements, patterns introducing zero variable bindings (such as `let Marker = m`) are strictly prohibited under the **Non-Vacuous Binding Invariant (`E0309: VacuousBindingError`)**.
- **Prelude Unwrapping**: Unwrapping via `inner(Marker)` evaluates to `()`.
- **Nominal Isolation**: A unit nominal type is an isolated nominal identity, strictly distinct from structural `()`. For example, `Result<Marker, E>` strictly requires `Ok(Marker)` and does NOT permit `Ok()`.

```ril
-- 1. Unit Nominal Types (zero-sized domain markers):
type Marker
type AdminToken

let m: Marker = Marker                 -- OK: bare identifier value construction
let raw_unit: () = inner(m)            -- OK: unwrap unit nominal wrapper evaluates to ()
let _ = m                              -- OK: explicit wildcard discard
-- let Marker = m                      -- Error [E0309]: 'let' pattern must bind at least one variable; 'Marker' introduces zero bindings

-- 2. Value-Wrapped Nominal Types:
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
-- let bad = UserId                    -- Error [E0301]: nominal wrapper 'UserId' requires 1 argument, found 0
```

### 3.7 Deep Immutability (`Immut<T>`)

`clone_immut(x)` deeply normalizes an object graph into an immutable value `Immut<T>`, guaranteeing permanent immunity to data races and mutation across threads.

```ril
type Document = { mut title: str, mut tags: []str }

let mut doc = Document.{ title: "Draft", tags: ["ril", "spec"] }
let frozen: Immut<Document> = clone_immut(doc)

-- Direct mutation on Immut<T> is rejected:
-- frozen.title = "Published"          -- Error [E0520]: cannot mutate fields of Immut<T>

-- Laundering Immut<T> into a mutable parameter is rejected:
fn modify_doc(mut d: Document) { d.title = "Changed" }
-- modify_doc(mut frozen)              -- Error [E0520]: cannot borrow Immut<Document> as 'mut'

let mut independent_copy = clone(doc)  -- OK: deep mutable clone
independent_copy.title = "Published"   -- OK: independent copy is mutable
```

### 3.8 Type Identity & Subtyping

1. **Width Subtyping**: Rejected on closed records. Permitted only via open row parameters (`{ id: int, .. }`).
2. **Depth Subtyping**: Mutable fields are invariant. Read-only fields are covariant.
3. **Callable Subtyping**: Parameters are contravariant; return types are covariant. State capabilities are covariant across the capability lattice (`&mut` $\sqsubset$ `&^mut`).

```ril
type Animal = { name: str }
type Dog = { name: str, breed: str }

-- Covariant read-only return:
type Getter<T> = fn() -> T
-- fn(d: Dog) -> Dog is a valid subtype of fn(d: Dog) -> Animal
```

### 3.9 Memory Model & Handle Invariants

1. **Handle-Level Immutability Invariant**: A binding declared with `let` establishes a completely immutable handle (neither reassignment nor in-place interior mutation is permitted).
2. **Pinned Mutable Handles (`let mut`)**: A binding declared with `let mut` establishes a pinned mutable handle over reference types. It permits in-place mutation of fields and elements, but statically rejects handle reassignment (`E0502`). Binding value types to `let mut` is statically rejected (`E0402`).
3. **Reassignable Mutable Variables (`var`)**: A binding declared with `var` establishes a reassignable mutable variable cell, permitting both slot reassignment and interior field mutation.
4. **Live Views (`let view x = obj`)**: A live view strips write permissions locally but dynamically observes concurrent or subsequent mutations on the underlying heap object. The target MUST be a pinned mutable root (`let mut` handle or `mut` parameter).
5. **Definite Mutation Invariant (`E0527`)**: Any binding declared with `let mut` or `var`, or parameter declared with `mut`, MUST undergo at least one reachable write operation along an executable path (`let mut` requires in-place mutation; `var` requires reassignment or mutation).

```ril
type Counter = { mut count: int }
let mut original = Counter.{ count: 0 }

let view v = original                  -- Live view into pinned root 'original'
-- v.count = 5                         -- Error [E0520]: cannot mutate through read-only view 'v'

original.count += 1
let observed = v.count                 -- observed is 1 (live view reflects mutation)

-- Pinned handle reassignment rejected:
-- original = Counter.{ count: 10 }    -- Error [E0502]: cannot reassign pinned mutable handle 'original'; use 'var'

-- Value type declared let mut rejected:
-- let mut bad_scalar = 42             -- Error [E0402]: value type 'int' has no interior mutability; use 'var'

-- Definite Mutation Invariant:
-- let mut unused_mut = Counter.{ count: 0 } -- Error [E0527]: variable 'unused_mut' declared 'let mut' but never modified
-- var unused_var = 10                 -- Error [E0527]: variable 'unused_var' declared 'var' but never modified
```

### 3.10 Path-Wise Copy-on-Write Functional Updates (`derive`)

**`derive(base, recipe)`**: Executes deep functional updates over reference data graphs via path-wise copy-on-write (structural sharing) mechanics. The mutating closure `recipe` mutates a derived proxy `next` in place, returning a fresh, unaliased immutable object without modifying `base`. Unmodified subtrees preserve pointer identity with `base`. Derived proxies cannot escape the recipe closure via return, external assignment, or closure publication (`E0607`).

#### Normative Rules for `derive`:
1. **Transactional Abort-Safety Invariant**: `derive` provides all-or-nothing transactional derivation. If `recipe` terminates abnormally via delimited early abort (§9.3) or runtime panic (§1.4):
   - `base` remains completely unmodified and structurally intact.
   - The in-flight derived proxy `next` and uncommitted path-copied nodes are discarded during stack frame unwinding without publishing a derived value, becoming unreachable garbage collected by tracing GC.
2. **Preservation of Commit-on-Write**: Ambient physical mutations to external memory performed by `recipe` prior to an abort remain permanently committed (§9.3) and are never rolled back.
3. **Derived Proxy Confinement (`E0607`)**: Derived proxies cannot escape the `recipe` closure via return value, external variable assignment, or closure publication (`E0607: DerivedProxyEscapeError`).

```ril
type UserSettings = { mut theme: str, mut notifications: bool }
type UserProfile = { mut name: str, mut settings: UserSettings }

let u1 = UserProfile.{
    name: "Alice",
    settings: UserSettings.{ theme: "dark", notifications: true },
}

-- 1. Normal derivation via path-wise copy-on-write:
let u2 = u1 |> derive \mut next -> {
    next.settings.theme = "light"
}
assert(u1.settings.theme == "dark")     -- u1 remains unchanged
assert(u2.settings.theme == "light")    -- u2 is a fresh updated copy
assert(u1.settings != u2.settings)      -- Modified subtree gets a fresh copy

-- 2. Transactional Abort-Safety: Delimited Early Abort (§9.3)
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

-- 3. Transactional Abort-Safety: Runtime Panic (§1.4)
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

-- 4. Derived proxy escape is strictly rejected:
-- let esc1 = u1 |> derive \mut next -> next     -- Error [E0607]: DerivedProxyEscapeError: derived proxy cannot escape 'derive' closure
-- let mut leaked = ()
-- u1 |> derive \mut next -> { leaked = next }   -- Error [E0607]: DerivedProxyEscapeError: derived proxy cannot escape 'derive' closure
```

### 3.11 Generic Parameters, Default Arguments & Value Sorts

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

1. **Trailing Defaults Invariant (`E0316`)**: If a generic parameter declares a default argument (`= Default`), all subsequent generic parameters in the same parameter list MUST declare default arguments.
2. **Telescopic Left-to-Right Scoping Invariant (`E0320`)**: A default argument expression $D_i$ may reference generic parameters declared to its left ($X_1, \dots, X_{i-1}$). Forward references and direct/indirect circular dependencies are statically rejected (`E0320`).
3. **Const Generic Evaluation & Purity Invariant (`E0810`, `E0323`)**: Const generic arguments evaluate at compile time within the pure symbolic domain ($\mathbf{Eff} = \emptyset, \mathbf{Cap} = \emptyset$). Non-constant runtime expressions passed to const parameters trigger `E0810`. Arguments failing sort constraints trigger `E0323`.
4. **No Untagged Literal Types (`E0301`)**: Concrete values (strings, integers, booleans) cannot serve as bare types. Discrete domain states MUST be modeled via tagged sum types (`type HttpMethod { Get, Post }`). Concrete values enter the type system strictly as compile-time arguments to const parameters (`Buffer<u8, 1024>`, `Matrix<f64, 4>`).
5. **Function Generic Default Prohibition (`E0317`)**: Function generic parameters cannot declare defaults (`fn f<T = int>` is rejected); function types are inferred bidirectionally at call sites.

```ril
-- 1. Sum Type with default type argument:
pub type Result<T, E = str> {
    Ok(T),
    Err(E),
}

let r1: Result<int> = Ok(42)                    -- OK: resolves to Result<int, str>
let r2: Result<int, int> = Err(404)             -- OK: explicit override of default E

-- 2. Nominal wrapper with default const generic and type parameter:
pub type Buffer<T = u8, cap: int = 1024>({
    data: []T,
    len: int,
})

let b1: Buffer = Buffer.{ data: [], len: 0 }    -- OK: resolves to Buffer<u8, 1024>
let b2: Buffer<u8, 2048> = Buffer.{ data: [], len: 0 } -- OK: explicit capacity override
let b3: Buffer<i32> = Buffer.{ data: [], len: 0 } -- OK: resolves to Buffer<i32, 1024>

-- 3. Dependent default arguments (Telescopic Left-to-Right):
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

-- 4. Rejection: Non-trailing default generic parameter (E0316):
-- type BadOrder<T = int, U> = { a: T, b: U }
-- Error [E0316]: generic parameter without default 'U' cannot follow generic parameter with default 'T'

-- 5. Rejection: Forward reference in default argument (E0320):
-- type BadForward<T = U, U = int> = { a: T }
-- Error [E0320]: default argument for 'T' contains forward reference to parameter 'U'

-- 6. Rejection: Function generic parameter with default (E0317):
-- fn bad_fn<T = int>(x: T) -> T { x }
-- Error [E0317]: function generic parameter 'T' cannot declare default type; functions rely on caller-site bidirectional inference

-- 7. Rejection: Literal types and untagged unions prohibited (E0301):
-- type BadMethod = "GET" | "POST"
-- Error [E0301]: literal values cannot be used as types; declare a tagged sum type instead

-- 8. Rejection: Runtime expression passed to const generic (E0810):
fn check_buf(runtime_size: int) {
    -- let bad_b: Buffer<u8, runtime_size> = Buffer.{ data: [], len: 0 }
    -- Error [E0810]: const generic parameter 'cap' expects compile-time constant, found runtime expression 'runtime_size'
}
```

---

## 4. Declarations & Bindings

### 4.1 Immutable Bindings (`let`)

```ebnf
LetDecl ::= "let" Pattern [ ":" TypeExpression ] "=" Expression
```

```ril
let x = 10                             -- Immutable integer binding
let (a, b) = (1, 2)                    -- Destructuring tuple binding
-- x = 20                              -- Error [E0501]: cannot reassign immutable binding 'x'

type Config = { capacity: int }
let cfg = Config.{ capacity: 64 }
-- let .{ mut capacity } = cfg         -- Error [E0521]: cannot destructure read-only record into 'mut' binding
```

### 4.2 Pinned Mutable Handles (`let mut`)

A binding declared with `let mut` binds a reference-type heap object as a **pinned mutable handle**. It permits in-place mutation of fields and elements, but statically forbids handle reassignment (`E0502`).

#### Normative Rules for Pinned Handles:
1. **Pinned Handle Invariant (`E0502`)**: A `let mut` handle is permanently pinned to its initial heap allocation. Reassigning the identifier (`handle = new_obj`) is statically rejected under `E0502: PinnedHandleReassignmentError`.
2. **Value Type Prohibition (`E0402`)**: Primitive value types (`int`, `bool`, `f64`, etc.) have no interior mutable fields. Declaring a value type as `let mut` is statically rejected under `E0402: ValueTypePinnedMutError`; mutable value types MUST be declared with `var`.
3. **Live View Stability**: Because a pinned mutable handle cannot be rebound, it provides guaranteed pointer stability as a mutable root for live views (`let view`).

```ebnf
LetMutDecl ::= "let" "mut" Pattern [ ":" TypeExpression ] "=" Expression
```

```ril
type Buffer = { mut items: []int }
let mut buf = Buffer.{ items: [1, 2] }

-- 1. In-place interior mutation is permitted:
buf.items !> Array::push(3)            -- OK: in-place write to pinned buffer

-- 2. Handle reassignment is statically rejected:
-- buf = Buffer.{ items: [] }          -- Error [E0502]: cannot reassign pinned mutable handle 'buf'; use 'var' if reassignment is intended

-- 3. Value types under let mut are rejected:
-- let mut count: int = 0              -- Error [E0402]: value type 'int' has no interior mutability; use 'var'

-- 4. Pattern-level pinned mutable destructuring:
type NodePair = { mut left: Buffer, mut right: Buffer }
let mut pair = NodePair.{ left: Buffer.{ items: [] }, right: Buffer.{ items: [] } }
let .{ mut left, mut right } = pair
left.items !> Array::push(10)          -- OK: 'left' is a pinned mutable handle
-- left = Buffer.{ items: [] }        -- Error [E0502]: cannot reassign pinned handle 'left'

-- 5. Definite Mutation Invariant:
-- let mut unused = Buffer.{ items: [] } -- Error [E0527]: variable 'unused' declared 'let mut' but never modified in-place
```

### 4.3 Reassignable Mutable Variables (`var`)

A binding declared with `var` establishes a **reassignable mutable variable cell**. It permits both variable slot reassignment (`x = ...`) and, when referencing a mutable object, interior in-place mutation (`x.field = ...`).

#### Normative Rules for `var`:
1. **Dual Permission**: A `var` binding allows both in-place field/element mutation and complete slot reassignment.
2. **Monotonic Anti-Laundering Degradation (`E0520`)**:
   - Reassigning a read-only reference into a `var` handle carrying mutable permissions is rejected under `E0520: MutabilityLaunderingError`.
   - When initialized from a read-only root (`var cursor = ro_list`), `var` inherits `ReadOnly` handle capability: slot reassignment is permitted (`cursor = cursor.next`), but interior mutation is statically rejected (`E0520`).
3. **Definite Mutation Invariant (`E0527`)**: A variable declared `var` MUST undergo at least one reachable write operation (reassignment or in-place mutation) along an executable path.

```ebnf
VarDecl ::= [ "pub" ] "var" Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
```

```ril
-- 1. Reassignable primitive scalar:
var counter = 0
counter += 1                           -- OK: reassignable scalar
counter = 10                           -- OK: direct reassignment
assert(counter == 10)

-- 2. Fully mutable reference variable:
var active_buf = Buffer.{ items: [1] }
active_buf.items !> Array::push(2)     -- OK: in-place mutation
active_buf = Buffer.{ items: [10, 20] } -- OK: handle reassignment permitted on 'var'
assert(len(active_buf.items) == 2)

-- 3. Read-only cursor over immutable structures:
type Node = { val: int, next: ?Node }
let ro_node2 = Node.{ val: 2, next: None }
let ro_node1 = Node.{ val: 1, next: Some(ro_node2) }

var cursor = ro_node1                  -- OK: 'cursor' is a reassignable ReadOnly handle
assert(cursor.val == 1)
cursor = ro_node2                      -- OK: reassignment permitted to matching ReadOnly type
-- cursor.val = 99                     -- Error [E0520]: cannot mutate field through read-only handle 'cursor'

-- 4. Pattern-level var destructuring:
var (start_idx, end_idx) = (0, 10)
start_idx += 1; end_idx -= 1           -- OK: both variables reassignable

-- 5. Definite Mutation Invariant:
-- var unused_var = 100                -- Error [E0527]: variable 'unused_var' declared 'var' but never modified
```

### 4.4 Scoped Resource Bindings (`let scoped`, `let scoped mut`)

Scoped bindings associate resources with lexical scopes. When exiting the enclosing scope (by normal completion, return, or unwinding), the cleanup handler executes in strict Last-In, First-Out (LIFO) order.

#### Normative Rules for Scoped Bindings:
1. **LIFO Destruction Order**: Scoped cleanups execute in strict reverse declaration order upon exiting the enclosing lexical block.
2. **Hermetic Cleanup Invariant (`E0616`, `E0617`)**: The `on_close` cleanup handler associated with `let scoped` MUST be effect-closed ($\mathop{\mathrm{Effects}} = \emptyset$, rejected under `E0616: ScopedCleanupEffectError`) and non-divergent (`@Div` prohibited, rejected under `E0617: ScopedCleanupDivergenceError`).
3. **Permitted In-Place Mutation**: In-place mutations on local and external mutable state (`&mut`, `&^mut`) within `on_close` are permitted under Commit-on-Write semantics (§9.3).
4. **Double-Fault Escalation**: If an unhandled panic occurs while executing an `on_close` handler during active stack unwinding (due to prior panic or delimited early abort), the runtime MUST NOT attempt secondary unwinding. In structured concurrency scopes, the task transitions immediately to `TaskFault::DoubleFaultFatal` (§9.5); in unsupervised execution frames, the process terminates immediately with an unrecoverable fatal abort.
5. **Prohibition of `var scoped` (`E0532`)**: Scoped resource bindings register cleanups to the enclosing lexical block in strict LIFO order. Reassigning a scoped variable would corrupt runtime block-exit unwinding. Therefore, `var scoped` and `scoped var` are statically prohibited (`E0532: ReassignableScopedResourceError`).

```ebnf
ScopedDecl ::= "let" "scoped" [ "mut" ] Identifier [ ":" TypeExpression ] "=" Expression
```

```ril
type Resource = { name: str, on_close: fn() -> () }

-- 1. Scoped bindings invoke cleanup upon exiting enclosing scope in strict LIFO order:
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
    -- second = Resource.{ name: "R3", on_close: \-> () } -- Error [E0502]: cannot reassign pinned scoped handle 'second'

    -- Scope exit triggers cleanup in strict LIFO order:
    -- 'second' closes FIRST, 'first' closes SECOND
}
assert(event_log == ["closed_R2", "closed_R1"])

-- 2. Iteration cleanup executes at the end of each iteration:
let mut iter_log: []str = []
for item in ["A", "B"] {
    let scoped res = Resource.{
        name: item,
        on_close: \-> iter_log !> Array::push("closed_" ++ item)
    }
    -- 'res' is cleaned up immediately before the next iteration begins
}
assert(iter_log == ["closed_A", "closed_B"])

-- 3. Static violations:
-- var scoped bad_reassign = Resource.{ name: "Bad", on_close: \-> () } -- Error [E0532]: scoped bindings cannot be declared 'var'
```

### 4.5 Live View Bindings (`let view`)

An explicit `let view` binding creates a live read-only observation handle into an existing reference object located on the managed GC heap. It strips write permissions locally while dynamically observing mutations performed through the underlying mutable root.

**Mutable Root Invariant**: The source expression of a `let view` binding MUST be an active pinned mutable root (`let mut` handle or `mut` parameter). Creating a live view over an immutable `let` binding is statically rejected (`E0531`). Creating a live view over a reassignable `var` variable is statically rejected (`E0531`) to guarantee pointer stability. Conversely, immutable bindings safely share read-only access with other ordinary `let` bindings (`let b = a`).

```ebnf
LetViewDecl ::= "let" "view" Identifier [ ":" TypeExpression ] "=" Expression
```

```ril
type Node = { mut val: int }
let mut original = Node.{ val: 10 }

-- 1. Live view aliases 'original' without write permissions:
let view observer = original
assert(observer.val == 10)

-- Writing through a view is statically prohibited:
-- observer.val = 20                   -- Error [E0520]: cannot mutate through read-only view 'observer'

-- Mutations to the underlying object are dynamically observed through the view:
original.val = 42
assert(observer.val == 42)             -- OK: live view reflects mutation

-- 2. Target Constraint: source must be a pinned mutable root
let immutable_node = Node.{ val: 100 }
-- let view bad_view = immutable_node   -- Error [E0531]: cannot create live view over immutable binding 'immutable_node' (source must be pinned mutable root)

var reassignable_node = Node.{ val: 200 }
-- let view bad_var_view = reassignable_node -- Error [E0531]: cannot create live view over reassignable variable 'reassignable_node' (source must be pinned mutable root)

-- Safe read-only sharing via ordinary let:
let safe_alias = immutable_node        -- OK: immutable bindings safely share read-only access
assert(safe_alias.val == 100)

-- 3. Concurrency Invariant:
-- A live mutable view cannot escape across a concurrent task boundary:
-- scope.fork(\-> observer.val)        -- Error [E0601]: cannot pass live mutable view across task boundary
```

### 4.6 Type Declarations & Opaque Types

```ebnf
TypeDecl       ::= [ "pub" ] [ "halt" ] "type" Identifier [ GenericParams ] [ WhereClause ] "=" TypeExpression
OpaqueTypeDecl ::= [ "pub" ] "opaque" "type" Identifier [ GenericParams ] [ WhereClause ] "=" TypeExpression
```

```ril
-- 1. Transparent Type Declarations:
pub type UserId = int                  -- Direct type alias, transparent across module boundaries
type Point = { x: int, y: int }        -- Local record type alias

-- 2. Opaque Type Declarations:
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

let token = create_token("secret_token_1234")?

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

-- Zero runtime boxing: storage in collections carries zero wrapper allocation:
let active_tokens: []SessionToken = [token]
let token_map: [SessionToken: int] = [token: 42]
```

### 4.7 Effect Declarations

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

### 4.8 External Interface Declarations (`.d.ril`)

External interface declarations are defined in dedicated declaration units with the `.d.ril` extension. A `.d.ril` module declares foreign signatures, opaque types, ambient constants, and exchange contract types without adding new keywords or dialects to the language.

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

#### Normative Rules for `.d.ril` Modules:
1. **Body Prohibition Invariant (`E0901`)**: Functions declared in `.d.ril` MUST NOT contain implementation bodies (`{ ... }`). Top-level constants MUST NOT declare initialization expressions (`= expr`). Supplying an implementation body or initializer in a `.d.ril` file is statically rejected under `E0901: BodyInDeclModuleError`.
2. **Missing Body Invariant (`E0902`)**: Omitting an implementation body from a function in a standard `.ril` module is statically rejected under `E0902: MissingBodyInStandardModuleError`. External signatures must reside in `.d.ril` modules.
3. **Opaque Nominal External Types**: A type declaration in `.d.ril` without a definition body (`pub type DomWindow`) defines an uninterpreted opaque nominal type. Direct field access (`x.field`), bracket indexing (`x[0]`), nominal unwrapping (`inner(x)`), pattern deconstruction, and direct value instantiation are statically rejected under `E0907: ForeignStructuralFieldPenetrationError`.
4. **Exchange Contract Types**: Transparent type aliases, records, and tagged sum types MAY provide full shape definitions in `.d.ril` to define exchange data contracts.
5. **Top-Level Immutability**: Top-level variables in `.d.ril` are restricted to immutable handles (`let`). Declaring `var` or `let mut` is statically rejected under `E0901`.
6. **Dual-Tier `where` Compatibility**: `DeclFunction` supports waist `where` (`SignatureWhereClause`) for aliasing signature callback types, but block-level `where` is omitted because foreign functions have no body block.

```ril
-- In file: platform/dom.d.ril

-- 1. Opaque nominal external types:
pub type DomWindow
pub type DomElement
pub type DomEvent

-- 2. Ambient external handle:
pub let WINDOW: DomWindow

-- 3. Transparent contract data types:
pub type QueryOptions = {
    timeout_ms: int,
    all_matches: bool,
}

pub type DomError {
    ElementNotFound,
    SecurityViolation(str),
}

-- 4. External function signatures:
pub fn query_selector(win: DomWindow, sel: str) -> Result<DomElement, DomError>
pub fn set_attribute(mut elem: DomElement, key: str, val: str) -> () &mut
pub fn add_listener(elem: DomElement, event_type: str, handler: EventHandler) -> () @Async
where
    type EventHandler = fn(DomEvent) -> () &mut

-- 5. Body prohibition in .d.ril (E0901):
-- pub fn bad_body() -> int { 42 }     -- Error [E0901]: BodyInDeclModuleError: functions in '.d.ril' cannot have an implementation body
-- pub let BAD_CONST: int = 100        -- Error [E0901]: BodyInDeclModuleError: constants in '.d.ril' cannot have an initializer expression

-- 6. Opaque penetration prohibited (E0907):
-- fn test_penetrate(elem: DomElement) {
--     let id = elem.id                 -- Error [E0907]: ForeignStructuralFieldPenetrationError: cannot access field on opaque type 'DomElement'
-- }
```

---

## 5. Expressions & Operators

### 5.1 Operator Precedence & Associativity

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

### 5.2 Arithmetic & Safe/Wrapping Operators

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

### 5.3 Bitwise & Shift Operators

```ril
let and_val = 0b1100 & 0b1010          -- 0b1000 (8)
let or_val  = 0b1100 | 0b1010          -- 0b1110 (14)
let xor_val = 0b1100 ^ 0b1010          -- 0b0110 (6)
let not_val = ~0b1100                  -- Bitwise NOT
let shl_val = 1 << 4                   -- 16
let shr_val = 64 >> 2                  -- 16
```

### 5.4 Relational, Equality & Containment Operators

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

### 5.5 Logical Operators

`&&` and `||` exhibit strict short-circuiting: the right operand is evaluated only when the left operand does not determine the result.

```ril
let valid_and = (p != None) && (p.x > 0) -- Right side not evaluated if p == None
let valid_or  = (items.len == 0) || (items[0] > 0) -- Right side not evaluated if items is empty
let negated   = !valid_and             -- Unary logical NOT
```

### 5.6 Range & Slicing Expressions

```ril
let r1 = 0..5                          -- Half-open range [0, 5)
let r2 = 0..=5                         -- Closed range [0, 5]

let arr = [10, 20, 30, 40, 50]
let slice = arr[1..4]                  -- [20, 30, 40]
let prefix = arr[..3]                  -- [10, 20, 30]
let suffix = arr[2..]                  -- [30, 40, 50]
```

### 5.7 Pipeline Operators (`|>`, `!>`)

1. **Linear Pipeline (`|>`)**: Passes the left expression as the first argument to the right callable: `x |> f` desugars to `f(x)`.
2. **Mutating Pipeline (`!>`)**: Passes the mutable left lvalue to the right mutating callable: `x !> f` desugars to `f(mut x)`.

```ril
let doubled = [1, 2, 3]
    |> Array::map(\x -> x * 2)
    |> Array::filter(\x -> x > 2)      -- Evaluates to [4, 6]

let mut items = [1, 2, 3]
items !> Array::push(4)                -- In-place mutation: items is now [1, 2, 3, 4]
```

### 5.8 Error & Fallback Operators (`?`, `??`, `?.`, `?[`)

1. **Postfix `?`**: Unwraps `Ok(v)` / `Some(v)`, or returns early with `Err(e)` / `None`.
2. **Fallback `??`**:
   - For `Option<T>`: Evaluates to `T` using the fallback value or supplier closure.
   - For `Result<T, E>`: Right operand MUST be an error-consuming closure `\err -> T`.
3. **Safe Navigation `?.`, `?[`**: Evaluates to `None` if the target is `None`; otherwise accesses field or index safely.

```ril
fn find_record(id: int) -> Result<str, str> {
    let user = fetch_user(id)?         -- Early return Err if fetch_user fails
    Ok(user.name)
}

let opt: ?int = None
let v1 = opt ?? 100                    -- 100 (Option fallback with default value)
let v2 = opt ?? \-> compute_default()  -- Option fallback with lazy supplier closure

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

### 5.9 Record Construction & Functional Update

```ril
type Point = { x: int, y: int, z: int }

let p1 = Point.{ x: 1, y: 2, z: 3 }
let p2 = Point.{ z: 10, ..p1 }         -- Functional record update: { x: 1, y: 2, z: 10 }
```

### 5.10 Assignments & Compound Assignments

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
-- pinned_buf = Buffer.{ capacity: 64 } -- Error [E0502]: cannot reassign pinned mutable handle 'pinned_buf'; use 'var'

-- Chained assignment is prohibited:
-- x = y = 10                          -- Error [E0701]: assignment chaining is prohibited
```

---

## 6. Control Flow & Pattern Matching

### 6.1 Block Expressions, Tail Values & Hoisted Block `where` Declarations

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

#### Invariants

1. **Declarative Partitioning (`E0703`, `E0702`)**:
   - Declarations (`fn`, `type`, `eff`) MUST NOT appear in `StatementSequence` (`E0703`).
   - Variable bindings (`let`, `let mut`, `var`) MUST NOT appear in `where` clauses (`E0702`).
2. **Local Effect Discharge (`E0618`)**:
   - Any local `eff` declared in `BlockWhereClause` MUST be completely discharged via an in-scope `with` handler within the enclosing block frame.
   - Local effects MUST NOT appear in outer `@Effect` annotations or escape into unhandled closures.
3. **Local Nominal Confinement (`E0315`)**:
   - Local nominal wrappers (`type Id(T)`) and sum types (`type S { ... }`) MUST NOT appear in the return type of the enclosing function. Structural type aliases (`type Alias = T`) are exempt.

```ril
-- 1. Mutually recursive functions and types hoisted in block 'where':
let total = {
    let base = compute_base()
    let parity = is_even(base)
    base
where
    fn compute_base() -> int { 100 }
    fn is_even(n: int) -> bool { if n == 0 { true } else { is_odd(n - 1) } }
    fn is_odd(n: int) -> bool { if n == 0 { false } else { is_even(n - 1) } }
}

-- 2. Local algebraic effect declared in 'where' and fully discharged locally:
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

-- 3. Prohibited: Declarations inside sequential statement stream (E0703):
-- let bad_statement = {
--     let x = 10
--     type Step = int                 -- Error [E0703]: IllegalSequentialDeclarationError: declarations of 'type' are prohibited in sequential statement stream; place in 'where' clause
--     eff Bail { exit() -> never }    -- Error [E0703]: IllegalSequentialDeclarationError: declarations of 'eff' are prohibited in sequential statement stream; place in 'where' clause
--     x + 1
-- }

-- 4. Prohibited: Variable bindings declared in 'where' (E0702):
-- let bad_where = {
--     base + 1
-- where
--     let base = 10                   -- Error [E0702]: InvalidWhereItemError: variable bindings cannot be declared in 'where' clause
-- }

-- 5. Prohibited: Undischarged local effect escaping block boundary (E0618):
-- fn bad_effect_leak() -> int @LocalStep { -- Error [E0618]: UndischargedLocalEffectError: local effect 'LocalStep' cannot escape enclosing block to function signature
--     LocalStep::tick()
--     1
-- where
--     eff LocalStep { tick() -> () }
-- }

-- 6. Prohibited: Local nominal type escaping function boundary (E0315):
-- fn bad_nominal_leak() -> Token {    -- Error [E0315]: EscapingLocalNominalTypeError: local nominal type 'Token' cannot escape declaring function
--     Token(42)
-- where
--     type Token(int)
-- }
```

### 6.2 Conditional Expressions (`if`)

`if` is an expression. Both branches must have compatible types. An `if` without an `else` evaluates to `()`.

```ril
let max = if a > b { a } else { b }

if logging_enabled {
    println("log message")             -- Evaluates to ()
}

-- Incompatible branch types are statically rejected:
-- let bad = if true { 10 } else { "error" } -- Error [E0301]: type mismatch, expected int, found str
```

### 6.3 Loop Expressions (`loop`, `while`, `for`)

```ril
-- 1. 'loop' with 'last' yielding a value:
var i = 0
let found = loop {
    i += 1
    if i == 5 { next }                 -- OK: skips to next iteration via 'next'
    if i == 10 { last i * 2 }          -- Loop evaluates to 20 via 'last'
}

-- 2. 'while' loop:
while i > 0 {
    i -= 1
}

-- 3. 'for' loop over ranges and collections:
var sum = 0
for x in 1..=5 {
    if x % 2 == 0 { next }             -- 'next' skips even numbers
    sum += x
}
assert(sum == 9)                       -- 1 + 3 + 5
```

### 6.4 Control Transfers (`last`, `next`, `return`)

Control transfers alter sequential evaluation order. Ril supports lexical control transfers (`last`, `next`, `return`) strictly scoped to the innermost enclosing loop or function. Ril deliberately omits loop labels to preserve syntactic clarity and guide multi-level escapes toward structured decomposition.

```ebnf
ControlTransfer ::= ( "last" [ Expression ] )
                  | "next"
                  | ( "return" [ Expression ] )
```

```ril
-- 1. 'last' terminates innermost loop (bare 'last' or 'last expr'):
var total = 0
for n in 1..=100 {
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

-- 2. 'next' advances innermost loop to next iteration:
var odd_sum = 0
for n in 1..=6 {
    if n % 2 == 0 { next }             -- Skips even iterations
    odd_sum += n
}
assert(odd_sum == 9)

-- 3. Function early return (bare 'return' or 'return expr'):
fn log_positive(val: int) {
    if val <= 0 { return }             -- Bare 'return': early exit from unit function
    println("positive: {val}")
}

fn search(matrix: [][]int, target: int) -> bool {
    for row in matrix {
        for cell in row {
            if cell == target { return true } -- 'return expr': early return with value
        }
    }
    false
}
```

### 6.5 Guarded Bindings (`let ... else`) & The Non-Vacuous Binding Invariant (`E0309`)

`let Pattern = expr else { Block }` matches a refutable pattern or diverges.

1. **Divergence Invariant**: The `else` block MUST diverge (evaluate to `never`).
2. **Universal Non-Vacuous Binding Invariant (`E0309`)**: All `let` statements (both simple `let Pattern = expr` and guarded `let Pattern = expr else { ... }`) MUST bind at least one variable into the enclosing lexical scope, with the sole exception of the explicit wildcard discard pattern `let _ = expr`. Patterns that introduce zero variable bindings (such as `let Marker = m`, `let () = expr`, `let Ok() = expr else { ... }`, `let None = expr else { ... }`, or `let _ = expr else { ... }`) are statically rejected (`E0309: VacuousBindingError`). To conditionally guard or test without binding variables, developers must use postfix `?`, boolean pattern tests (`if expr is Pattern`), or explicit `match` expressions.

```ril
fn process_account(data: [str: str]) -> Result<str, str> {
    -- The 'else' block MUST diverge (evaluate to 'never') and MUST bind >= 1 variable:
    let Some(id) = data["account_id"] else {
        return Err("missing account_id") -- OK: diverges via 'return', binds variable 'id'
    }

    -- Non-diverging 'else' is statically rejected:
    -- let Some(name) = data["name"] else {
    --     println("name missing")     -- Error [E0301]: 'else' branch of 'let ... else' must diverge
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
for entry in records {
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

### 6.6 Pattern Matching (`match`)

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

Matches are evaluated top-to-bottom. The compiler enforces exhaustiveness.

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
--     }                               -- Error [E0301]: non-exhaustive match expression, missing variant 'Point'
-- }
```

### 6.7 Pattern Syntax, Or-Patterns & Exhaustiveness

```ril
-- Or-patterns ('|') and pattern guards:
match status_code {
    200 | 201 | 204 -> "Success",
    400 | 401 | 404 -> "Client Error",
    500 | 502 | 503 -> "Server Error",
    _ -> "Unknown Code",
}

-- Or-patterns with variable bindings:
fn get_dimension(s: Shape) -> f64 {
    match s {
        Circle(dim) | Rect(dim, _) if dim > 0.0 -> dim,
        _ -> 0.0,
    }
}

-- Guards cannot prove exhaustiveness; fallback required:
-- fn bad_guard(n: int) -> str {
--     match n {
--         x if x >= 0 -> "positive",
--         x if x < 0  -> "negative",
--     }                               -- Error [E0301]: non-exhaustive match: compiler cannot prove guards cover all inputs
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
    -- Ok(a, b, c) -> println(a),        -- Error [E0301]: arity mismatch: variant 'Ok' payload expects 2 elements of type (int, str), found 3
    Err(err) -> println(err),
}

-- Unit payload constructor pattern (Result<(), str>):
let unit_res: Result<(), str> = Ok()
match unit_res {
    Ok() -> println("success"),          -- OK: matches () unit payload
    Err(e) -> println(e),
}
```

### 6.8 Flow-Sensitive Type Narrowing

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

#### Normative Semantic Rules & Invariants

1. **Environment Splitting**: Predicate $P$ splits context $\Gamma$ into true/false environments: $\Gamma \vdash P \rightsquigarrow (\Gamma_t, \Gamma_f)$.
2. **Division of Labor**:
   - `match`: Decomposes structures into new variables; exhaustiveness required.
   - `let ... else`: Extracts $\ge 1$ new bindings (`E0309`); `else` must diverge (`never`).
   - Narrowing (`if`/`while`): In-place refinement of existing bindings; binds 0 new variables.
3. **Non-Binding Predicates**: Pattern variables in `x is Variant(p)` are scoped strictly to trailing guards (`if guard`) and cannot escape to branch blocks (`E0301`).
4. **Payload Projection ($S|_V$)**: Testing `x is V` refines sum type $S$ to variant $S|_V$ (§3.5.1):
   - $n = 0$: No payload; projection raises `E0301`.
   - $n = 1$: Projected via `.0` (`p.0`). `?T != None` directly unboxes to `T`.
   - $n \ge 2$: Projected via positional tuple indices `.0`, `.1`, ..., `.(n-1)`.
   - Record: Projected via declared field names (`x.field`).
5. **Stability & Invalidation**:
   - `let`: Permanently narrowed across dominance region.
   - `var`: Reassignment (`=`, `+=`, `!>`) invalidates narrowing (`E0310`).
   - `let mut`: Tag identity is pinned (`E0502`); `mut` fields invalidate upon write.
6. **Transitive Latent Havoc**: Invoking a callable transitively carrying mutable capability $\&\{\text{mut } v\}$ (via callee, arguments, or active effect handlers) resets $v$ to $T_{\text{root}}$.
7. **Anti-Aliasing (`E0533`)**: Narrowing a `var` aliased by a live view (`let view`) or captured in a mutable closure (`&{mut x}`) is rejected (`E0533`). Copy to `let` to narrow.
8. **Generic Confinement**:
   - Testing bare type parameters (`x is T`) is rejected (`E0301`).
   - GADT equations on $x$ are local to $x$ and do not rebind $T$ elsewhere in scope.
   - Mutable fields preserve container invariance (§3.8).
9. **Dead Paths & Phase Ordering**:
   - Divergent branches (`never`) are pruned from joins ($\Gamma \sqcup \bot = \Gamma$).
   - Provably false predicates are rejected under `E0311`.
   - Dead-path pruning precedes Definite Mutation analysis (`E0527`); writes in dead paths do not count as reachable mutations.
10. **Bounded Analysis**:
    - **Path Bound**: Field paths are tracked up to depth 3 (`a.b.c`); deeper paths default to $T_{\text{root}}$.
    - **Loop Widening**: Unconverged loop variables widen to $T_{\text{root}}$ after $K = 3$ iterations.

```ril
-- 1. In-place optional unwrapping (?T -> T):
type User = { id: int, name: str }

fn process_user(u: ?User) -> str {
    if u != None {
        u.name                                 -- OK: 'u' narrowed to User; direct field access
    } else {
        "Anonymous"
    }
}

-- 2. Guard clause with early divergent return:
fn fetch_id(u: ?User) -> int {
    if u == None {
        return -1                              -- Diverges (never); pruned from join
    }
    u.id                                       -- OK: sequential flow inherits User
}

-- 3. Sum type variant discrimination via 'is' and payload projection:
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

-- 4. Short-circuit conjunction with immutable path chaining (depth <= 3):
type Account = { id: int, details: ?{ balance: int } }

fn check_solvent(acc: Account) -> bool {
    (acc.details != None) && (acc.details.balance > 0) -- OK: acc.details narrowed in right operand
}

-- 5. Loop body narrowing and post-loop refinement:
fn drain_cursor(var cursor: ?int) -> int {
    var total = 0
    while cursor != None {
        total += cursor                        -- OK: cursor narrowed to int in loop body
        cursor = None                          -- Invalidation: reset to ?int
    }
    assert(cursor == None)                     -- OK: post-loop inherits cond == false (None)
    total
}

-- 6. Reassignment invalidation (E0310):
fn test_invalidation() {
    var opt: ?int = Some(42)
    if opt != None {
        let _ = opt + 1                        -- OK: opt is int
        opt = None                             -- Reassignment: refinement invalidated
        -- let bad = opt + 2                   -- Error [E0310]: variable 'opt' was narrowed to 'int', but refinement was invalidated by reassignment; current flow type is '?int'
    }
}

-- 7. Contradictory narrowing rejection (E0311):
fn test_contradiction(g: Geometry) {
    if g is Geometry::Circle {
        -- if g is Geometry::Rect {            -- Error [E0311]: condition 'g is Geometry::Rect' is statically unsatisfiable; target is already narrowed to 'Geometry::Circle'
        --     println("unreachable")
        -- }
    }
}

-- 8. Aliased narrowing hazard rejection (E0533):
fn test_aliased_hazard() {
    var raw: ?int = Some(10)
    let view v = raw                           -- Live view aliases 'raw'
    -- if raw != None {                        -- Error [E0533]: cannot narrow mutable variable 'raw' because it is aliased by live view 'v'; bind to immutable 'let' before branching
    --     println(raw + 1)
    -- }
}

-- 9. Pattern bindings in 'is' cannot escape guard clause:
fn test_non_binding_predicate(g: Geometry) {
    if g is Geometry::Circle(r) if r > 5.0 {
        let radius = g.0                       -- OK: payload access via .0
        -- let escaped = r                     -- Error [E0301]: unresolved identifier 'r'; pattern bindings in 'is' are strictly scoped to guard clause
    }
}

-- 10. Transitive Latent Havoc via mutating call:
fn test_latent_havoc() {
    var count: ?int = Some(10)
    if count != None {
        let mut step = \-> &{mut count} { count = None }
        step()                                 -- Mutating call invalidates 'count'
        -- let bad_use = count + 1             -- Error [E0310]: variable 'count' was narrowed to 'int', but refinement was invalidated by mutating call 'step()'; current flow type is '?int'
    }
}

-- 11. Generic confinement: bare type parameter rejected:
fn test_generic_confinement<T>(x: Geometry) {
    -- if x is T {                             -- Error [E0301]: cannot test unconstrained generic type parameter 'T' in narrowing predicate
    --     println("invalid")
    -- }
}

-- 12. Dead-path mutation phase ordering:
fn test_dead_write_phase_ordering() {
    -- var unused: ?int = Some(10)            -- Error [E0527]: variable 'unused' declared 'var' is never modified along reachable paths
    -- if unused == None {
    --     unused = Some(20)                  -- Write in statically unreachable branch does not satisfy Definite Mutation Invariant
    -- }
}

-- 13. Path depth bound (depth <= 3 tracked; depth > 3 requires local 'let' anchor):
fn test_bounded_path_depth(root: { a: ?{ b: ?{ c: ?{ d: int } } } }) {
    if (root.a != None) && (root.a.b != None) && (root.a.b.c != None) {
        let c_node = root.a.b.c                -- OK: path depth 3 (root.a.b.c) tracked
        let d_val = c_node.d                   -- OK: access deeper fields through local anchor
    }
}
```

---

## 7. Functions, Closures & Callables

### 7.1 Named Function Declarations & Contrast Matrix

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

#### Dual-Tier `where` Invariants

1. **Signature `where` Scope (`SignatureWhereClause`, `E0704`)**:
   - `SignatureWhereClause` is restricted to `LocalTypeDecl` (`type`). Declaring `fn` or `eff` is statically rejected (`E0704`).
   - Types declared in `SignatureWhereClause` are in scope across the function signature and the function body block.
2. **Signature Reference Confinement (`E0706`)**:
   - Any type referenced in a function signature MUST be declared in `SignatureWhereClause` or an outer scope. Referencing types declared in `BlockWhereClause` is statically rejected (`E0706`).
3. **Downward Isolation (`E0705`)**:
   - Items in `SignatureWhereClause` MUST NOT reference items declared in `BlockWhereClause` (`E0705`). Items in `BlockWhereClause` MAY reference items from `SignatureWhereClause`.
4. **Collision Prohibition (`E0203`)**:
   - Declaring an identical identifier in both `SignatureWhereClause` and `BlockWhereClause` of the same function is statically rejected (`E0203`).
5. **Export Inlining**:
   - For `pub fn`, structural type aliases in `SignatureWhereClause` are canonically expanded in exported module interface artifacts (`.rilm`).

```ril
-- 1. Signature-level where for complex higher-order pipeline:
pub fn process_stream<T, R, E>(
    stream: []T,
    transform: TransformFn<T, R, E>,
    sink: AuditSink<R>,
) -> Result<[]R, E> @Async &{mut audit_log}
where
    type TransformFn<In, Out, Err> = fn(In) -> Result<Out, Err> @Fiber + Async &mut
    type AuditSink<Item>           = fn(Item) -> () &{mut audit_log} &closure
{
    var out: []R = []
    for stream as item {
        let res = transform(item)?
        sink(res)
        out !> Array::push(res)
    }
    Ok(out)
}

-- 2. Prohibited: Declaring 'fn' or 'eff' in SignatureWhereClause (E0704):
-- fn bad_waist_fn(x: int) -> int
-- where
--     fn helper(n: int) -> int { n * 2 }    -- Error [E0704]: InvalidSignatureWhereItemError: 'fn' cannot be declared in signature 'where' clause; place in block 'where' clause
--     eff Yield { emit(int) -> () }         -- Error [E0704]: InvalidSignatureWhereItemError: 'eff' cannot be declared in signature 'where' clause; place in block 'where' clause
-- {
--     helper(x)
-- }

-- 3. Prohibited: Downward reference from waist to block where (E0705):
-- fn bad_downward<T>(item: T) -> Wrapper
-- where
--     type Wrapper = { state: InternalState } -- Error [E0705]: DownwardScopeReferenceError: signature 'where' clause cannot reference 'InternalState' declared in inner block 'where' clause
-- {
--     Wrapper.{ state: .{ code: 0 } }
-- where
--     type InternalState = { code: int }
-- }

-- 4. Prohibited: Signature referencing type defined in block where (E0706):
-- fn bad_sig_target(cb: Callback) -> ()      -- Error [E0706]: SignatureTypeNotInWaistWhereError: type 'Callback' used in function signature must be declared in signature 'where' clause, not block 'where' clause
-- {
--     cb()
-- where
--     type Callback = fn() -> ()
-- }

-- 5. Prohibited: Duplicate declaration across waist and block tiers (E0203):
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
-- 1. Named Function: Module-level hoisted, zero environment allocation, static function pointer
pub fn calculate_tax(amount: int) -> int {
    amount * 20 / 100
}

-- 2. Stateless Anonymous Function: Pure function pointer, zero-cost (no environment allocation)
let tax_fn: fn(int) -> int = \amount -> amount * 20 / 100

-- 3. State-Capturing Closure: Carries environment pointer, type carries &closure
let rate = 20
let tax_closure: fn(int) -> int &closure = \amount -> amount * rate / 100

-- Invocations:
let r1 = calculate_tax(100)            -- OK: 20
let r2 = tax_fn(100)                   -- OK: 20
let r3 = tax_closure(100)              -- OK: 20
```

| Dimension | Named Function (`fn`) | Stateless Anonymous Function (`\x -> ...`) | Stateful Closure (`\x -> ... &closure`) |
| :--- | :--- | :--- | :--- |
| **Hoisting** | Module-wide newspaper ordering | Strictly lexical (definition before use) | Strictly lexical (definition before use) |
| **Environment Allocation** | Zero | Zero (bare machine code pointer) | Fat pointer (code pointer + environment struct) |
| **Type Representation** | Item identity / `fn(P) -> R` | `fn(P) -> R` | `fn(P) -> R &closure` |
| **Handle Requirement** | Direct call / `let` handle | Callable via `let` handle | `let` (read-only capture) or `let mut` / `var` (mut capture) |

### 7.2 Parameter Modes, Caller-Site Obligations & Defaults

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
-- add_score(player, 5)                -- Error [E0520]: argument to 'mut' parameter must be passed with 'mut'
-- let frozen_player = player
-- add_score(mut frozen_player, 5)     -- Error [E0520]: cannot borrow read-only handle 'frozen_player' as 'mut'
-- fn bad_inc(mut count: int) &mut {}  -- Error [E0401]: value types (int) cannot be declared as 'mut' parameters
-- fn noop_mut(mut u: User) &mut {}    -- Error [E0527]: 'mut' parameter 'u' declared but never modified
-- fn bad_rebind(mut u: User) &mut { u = User.{ name: "B", score: 0 } } -- Error [E0502]: cannot reassign pinned parameter 'u'
-- fn bad_var(var x: int) {}           -- Error [E0403]: 'var' parameters are prohibited in function signatures
```

#### Default Parameters and Named Arguments

1. Default expressions MUST be pure expressions (zero unhandled effects, zero state mutations).
2. Mutable parameters (`mut param: T`) CANNOT declare default values.
3. Explicit arguments evaluate strictly left-to-right before omitted defaults.
4. Named arguments allow order-independent binding at call sites.
5. Generic parameters on function declarations (`fn name<...>`) CANNOT declare default types or values (`E0317`). All function generic parameters must be inferred from value arguments via bidirectional type checking or explicitly specified at call sites.

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
-- fn bad_def(mut u: User = User.{ name: "A", score: 0 }) {} -- Error [E0401]: mutable parameter cannot have default
-- create_server("127.0.0.1", host: "duplicate")            -- Error [E0301]: parameter 'host' supplied both positionally and by name
-- fn bad_fn_gen<T = int>(x: T) -> T { x }                  -- Error [E0317]: function generic parameter 'T' cannot declare default type; functions rely on caller-site bidirectional inference
```

### 7.3 Anonymous Functions, Trailing Closures & Projection Accessors

```ebnf
AnonFnExpr    ::= "\" [ AnonParams ] "->" ( Expression | Block )
AnonParams    ::= AnonParam { "," AnonParam } [ "," ]
AnonParam     ::= [ "mut" ] Identifier [ ":" TypeExpression ]
AccessorExpr  ::= "\" AccessorNav AccessorField { AccessorNav AccessorField }
AccessorNav   ::= "." | "?."
AccessorField ::= Identifier | TupleIndex
TupleIndex    ::= Digit { Digit }
```

1. **Unary Desugaring Equivalence**: An `AccessorExpr` evaluates to a unary pure function projecting properties from its argument:
   - `\.field` desugars to `\x -> x.field`
   - `\.0` desugars to `\x -> x.0`
   - `\.field?.subfield` desugars to `\x -> x.field?.subfield`
   - `\?.field` desugars to `\x -> x?.field`
2. **Product Type Duality**:
   - `Identifier` statically projects named fields from records (`{...}`), nominal structs, or refined named variants. Unmatched fields trigger static error `E0301`.
   - `TupleIndex` statically projects 0-indexed positional components from tuples (`(T0, T1, ...)`) or refined positional variant payloads ($S|_V$). Positional indices are statically checked at compile time against tuple arity $n$ ($0 \le i < n$). Out-of-bounds indices trigger `E0301`.
3. **Safe Navigation Propagation**:
   - If any navigation segment uses safe navigation `?.`, evaluation short-circuits to `None` when the intermediate receiver is `None`. The resulting accessor closure return type is automatically lifted into `?T`.
4. **Collection Segregation**:
   - Dynamic collections (`[]T`, `[K: V]`, `Set<T>`) are not product types and cannot be projected via dot/accessor syntax directly (`E0301`). Element and key extractions require explicit bracket indexing (`\arr -> arr?[i]`) or higher-order combinators (`Array::first`, `Map::get`).

```ril
-- 1. Standard Anonymous Functions:
let double = \x -> x * 2
let sum = [1, 2, 3] |> Array::fold(0, \acc, x -> acc + x)

-- 2. Trailing Closure Syntax:
let doubled = [1, 2, 3] |> Array::map \x -> x * 2

fn run_job(f: fn() -> int) -> int { f() }
let job_res = run_job \-> 42

-- 3. Shorthand Projection Accessors:
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

-- 3b. Tuple positional index projection (\.index):
let pairs: [](int, str) = [(1, "Alice"), (2, "Bob")]
let ids = pairs |> Array::map(\.0)                            -- Evaluates to [1, 2]
let labels = pairs |> Array::map(\.1)                         -- Evaluates to ["Alice", "Bob"]

-- 3c. Mixed nested projection:
type Team = { id: int, leader: (str, int) }
let teams = [Team.{ id: 10, leader: ("Alice", 30) }]
let leader_ages = teams |> Array::map(\.leader.1)             -- Evaluates to [30]

-- 3d. Safe navigation projection (\.field?.subfield, \?.field):
let companies: []Company = [
    Company.{ name: "CorpA", dept: Some(Department.{ name: "Engineering", leader: Some(employees[0]) }) },
    Company.{ name: "CorpB", dept: None },
]
let leader_names = companies |> Array::map(\.dept?.leader?.name) -- Evaluates to [Some("Alice"), None]
let opt_depts: []?Department = [Some(Department.{ name: "Sales", leader: None }), None]
let dept_names = opt_depts |> Array::map(\?.name)                -- Evaluates to [Some("Sales"), None]

-- Rejections:
-- let bad_idx = pairs |> Array::map(\.2)                     -- Error [E0301]: tuple index 2 out of bounds for (int, str)
-- let bad_field = employees |> Array::map(\.age)             -- Error [E0301]: unknown field 'age' on type 'Employee'
-- let bad_arr = [[1, 2], [3]] |> Array::map(\.0)             -- Error [E0301]: collections do not have named fields or static tuple projections
```

### 7.4 Closures, Factory Signatures & Lexical Environments

1. **`&closure`**: Marks a callable value whose body captures variables from an enclosing scope.
2. **`&capture`**: Marks a factory function that allocates and returns an escaping closure.
3. Invoking closures that capture **read-only** variables requires only a standard `let` handle.
4. Invoking closures that capture **mutable** variables strictly requires a `let mut` handle.

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
-- frozen_acc(5)                       -- Error [E0520]: cannot invoke mutable-capturing closure via read-only handle 'frozen_acc'

-- Nested Closures and Flat Chain Elaboration:
fn make_nested_multiplier(factor: int) -> (fn(int) -> (fn(int) -> int &closure) &closure) &capture {
    let base_multiplier = factor
    \multiplier_step -> {
        let intermediate = base_multiplier * multiplier_step
        \x -> x * intermediate         -- Elaborates flat capture set: &{closure make_nested_multiplier, base_multiplier, intermediate}
    }
}
```

### 7.5 Higher-Order Functions & Automatic Effect / Capability Forwarding

Higher-order functions forward both algebraic effects and state capabilities transparently:

```ril
fn apply<T, R>(x: T, f: fn(T) -> R) -> R {
    f(x)                               -- Transparently forwards f's effects and state capabilities
}

-- 1. Purity Conservation: Pure argument incurs ZERO obligations
let r_pure = apply(10, \x -> x * 2)   -- Pure call: zero effect, zero capability

-- 2. Algebraic Effect Forwarding:
eff Logger { log(str) -> () }
fn logged_square(n: int) -> int @Logger {
    Logger::log("calculating")
    n * n
}
fn caller_with_effect() -> int @Logger {
    apply(5, logged_square)            -- Requires @Logger on caller_with_effect
}

-- 3. State Capability Forwarding (&mut):
type Counter = { mut val: int }
let mut my_counter = Counter.{ val: 0 }
fn bump(mut c: Counter) &mut { c.val += 1 }

fn mutate_caller(mut c: Counter) &mut {
    apply(mut c, \mut target -> bump(mut target)) -- Transparently forwards &mut capability
}

-- 4. External State Capability Forwarding (&{mut ident}):
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

## 8. State & Capability Tracking

### 8.1 Local Mutation Purity & Local Capability Discharge

A function that mutates locally allocated variables that do not escape retains a purely functional external interface. Capability obligations for frame-confined variables are **discharged locally**:

```ril
type Buffer = { mut items: []int }
fn append_val(mut b: Buffer, v: int) &mut { b.items !> Array::push(v) }

-- 1. Pure function with internal primitive mutation:
fn compute_sum(n: int) -> int {
    var total = 0
    var i = 1
    while i <= n {
        total += i
        i += 1
    }
    total                              -- Pure to callers: signature is fn(int) -> int
}

-- 2. Local Capability Discharge with reference types and &mut callees:
fn generate_sequence(count: int) -> []int {
    let mut local_buf = Buffer.{ items: [] }
    var i = 0
    while i < count {
        append_val(mut local_buf, i)   -- &mut discharged locally: local_buf does not escape
        i += 1
    }
    local_buf.items                    -- Pure: signature carries NO &mut!
}

-- 3. Local Discharge of Retained Sharing (&^mut):
type NodeHub = { mut nodes: []int }
fn link(mut hub: NodeHub, node: int) &^mut { hub.nodes !> Array::push(node) }

fn test_internal_hub() -> int {
    let mut local_hub = NodeHub.{ nodes: [] }
    var local_node = 42
    link(mut local_hub, local_node)    -- &^mut discharged locally: all origins frame-confined
    len(local_hub.nodes)               -- Pure: signature carries NO &^mut!
}
```

### 8.2 Parameter Mutation (`&mut`)

A function mutating any borrowed parameter MUST declare `&mut`.

```ril
fn clear_items(mut list: []int) &mut {
    list !> Array::truncate(0)         -- OK: declared &mut
}

-- Missing capability annotation is statically rejected:
-- fn bad_clear(mut list: []int) {     -- Error [E0510]: missing state capability '&mut'
--     list !> Array::truncate(0)
-- }
```

### 8.3 Retained Mutable Sharing (`&^mut`, `&{^mut ident}`)

Retained mutable sharing occurs when execution creates a persistent writable access path that survives the call or closure publication boundary ($\ge 2$ independent surviving write paths). Origin identities survive intermediate local bindings: forwarding an external or borrowed reference through a local `let mut` handle does not alter its storage origin or discharge capability obligations. Conversely, allocating a fresh mutable reference that escapes solely through a single closure creates exactly 1 surviving write path and requires only `&capture`, while exposing multiple surviving handles creates $\ge 2$ write paths and requires `&^mut`.

```ril
type Hub = { mut entries: []Entry }
type Entry = { mut id: int }

-- 1. Parameter Mutation ONLY (&mut):
-- Writable access to 'e' terminates at return; no persistent alias is created
fn touch_entry(mut e: Entry) &mut {
    e.id += 1
}

-- 2. Anonymous Retained Mutable Sharing (&^mut):
-- Retains writable alias to parameter 'e' inside parameter 'h'; both survive the call
fn register_entry(mut h: Hub, mut e: Entry) &^mut {
    h.entries !> Array::push(e)        -- Survives call: 'e' is now aliased through 'h'
}

-- 3. External Named Retained Mutable Sharing (&{^mut ident}):
-- Stashes a mutable parameter into an external global container
let mut global_hub = Hub.{ entries: [] }

fn publish_entry(mut e: Entry) &{^mut global_hub} {
    global_hub.entries !> Array::push(e) -- Survives call: 'e' is retained in global_hub
}

-- 4. Returning a closure that captures and shares external mutable state:
var active_connections = 0

fn make_connection_ticker() -> (fn() -> int &{mut active_connections}) &{^mut active_connections} {
    \-> {
        active_connections += 1
        active_connections
    }
}

-- 5. Intermediate Forwarding & Origin Tracking:
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
-- Error [E0510]: missing capability '&{^mut global_session}'

fn make_param_ticker(mut s: Session) -> (fn() -> int &closure) &^mut {
    let mut forwarded = s              -- Intermediate local handle
    \-> {
        forwarded.count += 1
        forwarded.count
    }                                  -- Survives call: caller and closure both retain write paths to 's'
}

-- 6. Write Path Counting (Encapsulated Allocation vs. Retained Sharing):
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
-- Error [E0529]: excessive capability '&^mut', private allocation has no surviving aliases

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

### 8.4 External State Tracking (`&{ident}`, `&{mut ident}`)

Accessing module-level or outer lexical bindings without passing them as parameters requires explicit named capability annotations:

```ril
let APP_CONFIG_NAME = "Production"
var transaction_count = 0

-- 1. Read-only external access:
fn get_config_name() -> str &{APP_CONFIG_NAME} {
    APP_CONFIG_NAME                    -- OK: declared &{APP_CONFIG_NAME}
}

-- 2. Mutable external access:
fn record_transaction() -> () &{mut transaction_count} {
    transaction_count += 1             -- OK: declared &{mut transaction_count}
}

-- 3. Static errors on missing annotations:
-- fn bad_read() -> str { APP_CONFIG_NAME }          -- Error [E0510]: missing capability '&{APP_CONFIG_NAME}'
-- fn bad_write() { transaction_count += 1 }        -- Error [E0510]: missing capability '&{mut transaction_count}'

-- 4. Prohibition of Anonymous Concealment:
-- fn conceal_write() &mut { transaction_count += 1 } -- Error [E0510]: cannot use anonymous '&mut' to conceal external 'transaction_count'
```

### 8.5 Closure Capabilities & Handle Invocation Permissions

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
-- read_only_counter()                 -- Error [E0520]: cannot invoke mutable-capturing closure via read-only handle 'read_only_counter'

-- Read-only capturing closure:
fn create_greeter(prefix: str) -> (fn(str) -> str &closure) &capture {
    \name -> prefix ++ ", " ++ name    -- Captures read-only 'prefix'
}

let greeter = create_greeter("Hello")  -- Bound as immutable 'let greeter'
let msg = greeter("Alice")             -- OK: read-only capture can be invoked via 'let' handle!
```

### 8.6 Law of Exclusivity & Cross-Argument Disjointness

For every argument passed to a `mut` parameter, its memory path MUST be pairwise disjoint from every other argument and active closure capture in that call:

```ril
type Point = { mut x: int, mut y: int }
type Buffer = { mut size: int, mut data: []int }

fn swap(mut a: int, mut b: int) &mut {
    let tmp = a; a = b; b = tmp
}
fn append_buf(src: Buffer, mut dst: Buffer) &mut { ... }
fn modify_with(mut b: Buffer, cb: fn() -> ()) &mut {
    cb()
    b.size += 1
}

-- 1. Record Field Disjointness:
let mut pt = Point.{ x: 1, y: 2 }
swap(mut pt.x, mut pt.y)               -- OK: pt.x ∩ pt.y = ∅ (provably distinct fields)
-- swap(mut pt.x, mut pt.x)            -- Error [E0523]: MutMutAliasingConflictError: overlapping mutable borrow on 'pt.x'

-- 2. Read-Mut Cross-Argument Conflicts:
let mut buf = Buffer.{ size: 0, data: [] }
-- append_buf(buf, mut buf)            -- Error [E0524]: ReadMutAliasingHazardError: 'buf' borrowed as mut while read-only borrowed

-- 3. Array Element Disjointness:
let mut numbers = [10, 20, 30]
swap(mut numbers[0], mut numbers[1])   -- OK: distinct constant indices 0 and 1
let idx_a = 0; let idx_b = 0
-- swap(mut numbers[idx_a], mut numbers[idx_b]) -- Error [E0523]: dynamic indices may overlap

-- 4. Callback / Closure Aliasing Overlap:
let mut target = Buffer.{ size: 10, data: [1, 2] }

-- Callback captures read-only path overlapping mutable argument 'mut target':
-- modify_with(mut target, \-> { println(target.size) })
-- Error [E0524]: ReadMutAliasingHazardError: callback captures read-only path 'target' overlapping 'mut target'

-- Callback captures mutable path overlapping mutable argument 'mut target':
-- modify_with(mut target, \-> { target.size = 0 })
-- Error [E0523]: MutMutAliasingConflictError: callback captures mutable path 'target' overlapping 'mut target'
```

### 8.7 Monotonic Permission Degradation & Anti-Laundering Matrix

Permissions degrade monotonically ($\text{Mut} \succ \text{ReadOnly} \succ \text{None}$). Converting a read-only handle into a mutable capability is statically rejected under the closed diagnostic matrix:

```ril
type UserDoc = { mut title: str, mut score: int }

-- E0520: MutabilityLaunderingError (binding/assigning read-only to let mut or mutable var, or mutating through view)
let doc = UserDoc.{ title: "Draft", score: 0 }
-- doc.score = 10                      -- Error [E0520]: cannot mutate field through read-only handle 'doc'
-- let mut laundered = doc             -- Error [E0520]: cannot bind read-only handle to 'let mut'
let mut other_doc = UserDoc.{ title: "Active", score: 5 }
other_doc.score = 10                  -- OK: mutable handle mutated
-- other_doc = doc                    -- Error [E0502]: cannot reassign pinned mutable handle 'other_doc'; use 'var'
var reassignable_doc = UserDoc.{ title: "Active", score: 5 }
-- reassignable_doc = doc             -- Error [E0520]: cannot reassign read-only handle 'doc' to mutable handle 'reassignable_doc'
fn pass_to_mut(mut u: UserDoc) &mut { u.score += 1 }
-- pass_to_mut(mut doc)                -- Error [E0520]: cannot borrow read-only handle 'doc' as 'mut'

-- E0521: DestructureMutabilityLaunderingError (destructuring read-only into mut fields)
-- let .{ mut score } = doc            -- Error [E0521]: cannot bind read-only field to 'mut' pattern

-- E0522: ContainerMutabilityLaunderingError (injecting read-only reference into mutable container)
let mut doc_list: []UserDoc = []
-- doc_list !> Array::push(doc)        -- Error [E0522]: cannot store read-only reference 'doc' into mutable array
let mut detached = doc |> clone        -- OK: clone() produces independent detached mutable duplicate
doc_list !> Array::push(detached)      -- OK: detached mutable root stored into mutable container

-- E0523 & E0524: Mut-Mut and Read-Mut aliasing hazards (see §8.6)

-- E0525: SpreadLaunderingError (shallow-spreading read-only record into let mut root)
-- let mut spread_doc = UserDoc.{ ..doc, score: 99 } -- Error [E0525]: shallow spread of read-only record into 'let mut'

-- E0526: CollectionMutationDuringIterationError (mutating collection while iterating over it)
let mut nums = [1, 2, 3]
for item in nums {
    -- nums !> Array::push(item)       -- Error [E0526]: cannot mutate 'nums' in place while iterating in 'for' loop
}

-- E0527: UnusedMutableBindingError (declared 'var', 'let mut', or 'mut' parameter but never modified)
-- var never_written = 42              -- Error [E0527]: variable 'never_written' declared 'var' but never modified
-- let mut unused_doc = UserDoc.{ title: "X", score: 0 } -- Error [E0527]: variable 'unused_doc' declared 'let mut' but never modified in place
-- fn noop_mut(mut u: UserDoc) &mut {} -- Error [E0527]: 'mut' parameter 'u' declared but never modified

-- E0528: ReturnMutabilityLaunderingError (returning read-only parameter into caller let mut)
fn inspect_user(u: UserDoc) -> UserDoc { u }
let user_in = UserDoc.{ title: "Alice", score: 10 }
-- let mut stolen = inspect_user(user_in) -- Error [E0528]: cannot bind return value originating from read-only parameter to 'let mut'
let inspected = inspect_user(user_in)     -- OK: caller receives as read-only handle

-- E0529: ExcessiveCapabilityAnnotationError (over-annotating beyond minimal required capabilities)
-- fn pure_add(a: int, b: int) -> int &mut { a + b } -- Error [E0529]: function does not mutate parameters or state

-- E0530: IllegalCapabilityCloneImmutError (target carries active capabilities: neither clonable nor freezable)
let mut counter_handle = create_counter(0)
-- let bad_clone = clone(counter_handle)       -- Error [E0530]: cannot clone active capability or closure
-- let bad_immut = clone_immut(counter_handle) -- Error [E0530]: target carrying active capabilities is neither clonable nor freezable into Immut<T>

-- E0531: ImmutableTargetViewError (creating a live view over an immutable binding)
let immutable_doc = UserDoc.{ title: "Frozen", score: 100 }
-- let view bad_v = immutable_doc       -- Error [E0531]: cannot create live view over immutable binding 'immutable_doc' (source must be mutable root)
let safe_alias = immutable_doc        -- OK: immutable binding safely shared across read-only handles
```

### 8.8 Callable Signature Abstraction

Concrete captured variable names abstract behind `&closure`. Retained mutable sharing `&{^mut ident}` cannot be erased: it MUST abstract to both `&closure` and anonymous `&^mut`. Casting stateful callables to unannotated pure functions is strictly rejected.

```ril
var session_data = 0
let concrete_worker: fn(int) -> int &{mut session_data} = \delta -> {
    session_data += delta
    session_data
}

-- 1. Valid Abstraction: Hiding variable name behind &closure
type Worker = fn(int) -> int &closure
let abstract_worker: Worker = concrete_worker -- OK: concrete &{mut session_data} satisfies &closure

-- 2. Retained Sharing Abstraction: MUST retain &^mut
let mut hub = Hub.{ entries: [] }
let concrete_stashing: fn(Entry) -> () &{^mut hub} = \mut e -> {
    hub.entries !> Array::push(e)
}

type StashingWorker = fn(Entry) -> () &closure &^mut
let abstract_stashing: StashingWorker = concrete_stashing -- OK: preserves &^mut hazard

-- 3. Illegal Hazard Erasure:
-- type BadWorker = fn(Entry) -> () &closure
-- let illegal: BadWorker = concrete_stashing -- Error [E0510]: cannot erase '&^mut' hazard through abstraction
-- let pure_cast: fn(int) -> int = concrete_worker -- Error [E0301]: cannot erase '&closure' to pure function
```

---

## 9. Algebraic Effects & Concurrency

### 9.1 Effect Declarations & Operation Signatures

Effects define abstract operation tags that callers invoke and enclosing handlers intercept. An effect operation signature is an ordinary callable signature: it declares argument types, return types, and optional capabilities (`&mut`, `&^mut`).

When an effect operation requires in-place mutation (e.g., writing into a caller-supplied buffer), it explicitly declares `&mut` on its operation signature. Callers invoking the operation and handlers servicing it must track, forward, or discharge this capability under standard capability tracking rules (§8). Concurrency boundaries (`scope.fork`, `Parallel::map`) enforce Data-Race Freedom (DRF-SC) directly through capability checking: any value or closure crossing a concurrency boundary must not carry live mutable capabilities (`&mut`, `&^mut`, `&{mut var}`), rejected statically under `E0601: CrossThreadDataRaceHazardError`. Concurrency boundaries simultaneously enforce Algebraic Control Confinement: child tasks must be effect-closed under user-defined effects (§9.5), rejected statically under `E0615: CrossTaskUnhandledEffectError`.

```ril
-- 1. Pure Effect Operations & Ambient Context:
eff Console {
    print(str) -> (),
    read_line() -> str,
}

eff Context<T> {
    ask() -> T,                        -- OK: Ambient context value
}

-- 2. Effect Operations Declaring Mutation Capabilities:
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

-- 3. Concurrent Task Boundary: DRF-SC Capability Enforcement:
fn concurrent_boundary_check() {
    let immut_data = "immutable configuration"
    let mut local_buf = [0u8, 0u8, 0u8]

    scope(\mut s -> {
        -- OK: Immutable value has zero mutable capabilities, safely crosses task boundary:
        s.fork(\-> {
            immut_data
        })

        -- Error [E0601]: CrossThreadDataRaceHazardError: live mutable capability cannot cross task boundary
        -- s.fork(\-> {
        --     local_buf[0] = 1u8
        -- })
        Ok()
    })
}
```

### 9.2 Effect Handlers (`with`)

`with` intercepts operations within its lexical scope, discharging the effect from the enclosing function's signature. When placed within a block, `with HandlerSpec` establishes the active deep handler for all subsequent expressions and statements in the remainder of that enclosing block. Handlers in Ril are **deep handlers**: evaluating `resume v` does not discard the handler; it remains active for all subsequent effect invocations until the block terminates.

Closures constructed in a scope with an active `with` handler **automatically capture the handler** into their heap environment (`&closure`), safely discharging the effect from the closure's public signature. Closures carrying unhandled effects that escape to heap records without an in-scope handler are statically rejected (`E0614`). Automatic handler capture (`&closure`) is strictly task-confined: handlers established in an enclosing scope MUST NOT be captured into closures crossing concurrent task boundaries (`scope.fork`, `Parallel::map`). Closures passed across concurrent task boundaries must be effect-confined (§9.5), rejected under `E0615` if unhandled effects or externally captured handlers are present.

```ebnf
WithExpr    ::= "with" HandlerSpec
HandlerSpec ::= "{" HandlerArm { "," HandlerArm } [ "," ] "}" | HandlerArm
HandlerArm  ::= QualifiedName "(" [ PatternList ] ")" "->" Expression
ResumeExpr  ::= "resume" Expression
```

```ril
-- 1. Multi-Arm Statement Handler (like match block):
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

-- 2. Single-Arm Statement Handler:
fn run_config() -> str {
    with Context::ask() -> resume "Production"
    Context::ask()                     -- Intercepted by single-arm handler
}

-- 3. Automatic Handler Capture in Escaping Closures:
type Button = { label: str, on_click: fn() -> () }

fn make_button() -> Button {
    with Console::print(msg) -> resume ()

    -- Closure invokes Console::print. Because 'with Console' is active in scope,
    -- compiler automatically captures the handler into closure environment:
    let cb = \-> Console::print("Button clicked!")
    -- 'cb' has type fn() -> () &closure (@Console discharged!)

    Button.{ label: "Save", on_click: cb } -- OK: safely stored in heap record!
}

-- 4. Escaping Effect Closure Error (E0614):
-- fn bad_escape() -> Button {
--     let unhandled_cb = \-> Console::print("Dangling")
--     -- Error [E0614]: EscapingEffectClosureError: closure with unhandled effect '@Console' escapes to heap record without in-scope handler
--     Button.{ label: "Bad", on_click: unhandled_cb }
-- }
```

### 9.3 Affine Resumption (`resume`) and Delimited Early Abort

`resume` is strictly one-shot (affine). Invoking `resume` more than once or escaping the handler arm is a compile-time static error. Returning from a handler arm without calling `resume` triggers delimited early abort, unwinding active `let scoped` resources in LIFO order. Physical memory mutations performed prior to the abort remain permanently committed (Commit-on-Write invariant; physical mutations are never rolled back).

```ril
-- 1. Affine Resumption Violation: invoking resume more than once
fn bad_double_resume() -> int {
    with Op::query() -> {
        let first = resume 1
        -- let second = resume 2        -- Error [E0610]: affine resumption 'resume' invoked more than once
        first
    }
    Op::query()
}

-- 2. Escaping Resumption Violation: resume escaping the handler arm
fn bad_escaping_resume() -> fn() -> int {
    with Op::query() -> {
        let esc = \-> resume 42         -- Error [E0611]: affine resumption 'resume' cannot escape handler arm
        esc
    }
    Op::query()
}

-- 3. Delimited Early Abort with Proven LIFO Cleanup & Commit-on-Write Memory:
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

### 9.4 Built-in Effects (`@Async`, `@Fiber`, `@Concurrent`, `@Div`)

Ril provides four foundational built-in algebraic effects tracking execution capabilities:

1. **`@Fiber` (Cooperative Fiber Control)**: Low-level cooperative scheduling primitives (`yield`, `park`, `unpark`). Purely cooperative execution-quantum transfer without concurrent task branching authority.
2. **`@Concurrent` (Structured Concurrency)**: High-level concurrent task forking, joining, racing, and timeout mechanics.
3. **`@Async` (Suspendable I/O)**: An effect alias `{Fiber, Concurrent}` tracking uncolored asynchronous computations.
4. **`@Div` (Divergence Tracking)**: Tracks potential non-termination in unbounded loops and general recursive functions. Total functions (`halt fn`) strictly prohibit `@Div`.

The sub-effect lattice satisfies $\emptyset \subset \{\text{Fiber}\} \subset \{\text{Fiber}, \text{Concurrent}\} = \text{Async}$.

#### Normative Rules for Built-in Effects:
1. **Least-Privilege Leaf I/O Principle (`@Fiber`)**: Leaf I/O operations requiring cooperative suspension without forking child tasks MUST declare only `@Fiber`. Holding `@Fiber` does not grant authority to fork concurrent tasks (`@Concurrent`), preserving frame containment and single-fiber DRF-SC invariants.
2. **Compound Asynchronous Workflows (`@Async`)**: Functions that both suspend on I/O and manage concurrent child tasks declare `@Async`.
3. **Decoupling Quantum Scheduling from Value Generators**: Cooperative scheduling operations declared within `eff Fiber` (`yield() -> ()` and `park() -> ()`) are strictly untyped quantum transfer primitives. Value-emitting streams MUST be modeled via user-defined algebraic effects (e.g., `eff Yield<T> { emit(T) -> () }`), evaluated as internal push streams under one-shot delimited resumption (`resume ()`). External pull iterators cannot escape `resume` past handler arm boundaries (`E0611`) and are constructed via compiler-lowered state machines or fiber channels.

```ril
-- 0. Built-in Fiber Effect Declaration:
eff Fiber {
    yield() -> (),                     -- Relinquishes quantum to runtime scheduler
    park() -> (),                      -- Suspends execution until external event/wakeup
    unpark() -> (),                    -- Awakens a parked fiber context
}

-- 1. Leaf I/O Suspension Principle (@Fiber):
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

-- 2. Compound Asynchronous Workflow (@Async = {Fiber, Concurrent}):
fn fetch_pipeline(url: str) -> Result<str, TaskFault> @Async {
    let raw = read_socket_chunk(80)    -- Inherits @Fiber
    scope(\mut s -> {                  -- Requires @Concurrent (present in @Async)
        let worker = s.fork(\-> parse(raw))
        let parsed = worker.join()?
        Ok(parsed)
    })
}

-- 3. Cooperative Fiber Yielding (@Fiber):
fn cooperative_worker(mut count: int) -> () @Fiber {
    while count > 0 {
        count -= 1
        Fiber::yield()                  -- Yields execution quantum to runtime scheduler
    }
}

-- 4. Value-Streaming Generator Orthogonality:
eff Yield<T> {
    emit(value: T) -> ()
}

fn range_stream(mut cur: int, max: int) @Yield<int> {
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

-- (b) Orthogonal Composition: Suspendable Async Generator:
fn stream_remote_chunks(fd: int) -> () @Yield<[]u8> @Fiber {
    while true {
        let chunk = read_socket_chunk(fd)
        if len(chunk) == 0 { last }
        Yield::emit(chunk)             -- Orthogonally composes @Yield<[]u8> and @Fiber
    }
}

-- 5. Divergence vs. Total Functions (@Div):
fn collatz(n: int) -> int @Div {
    if n <= 1 { 1 }
    else if n % 2 == 0 { collatz(n / 2) }
    else { collatz(3 * n + 1) }
}

-- Total function: provably terminates; @Div is strictly forbidden
halt fn factorial(n: int) -> int {
    if n <= 1 { 1 } else { n * factorial(n - 1) }
}
-- halt fn bad_total(n: int) -> int {  -- Error [E0820]: 'halt fn' contains uncertified recursion or unbounded loop
--     collatz(n)
-- }
```

### 9.5 Structured Concurrency (`scope`) & Isolated Panic Containment

All concurrent child tasks must be forked within a structured `scope`. A parent scope cannot exit until all child tasks finish. Panics and task failures in child tasks are isolated at the scope boundary and resolve to `Result<T, TaskFault>` (`TaskFault::Panicked`, `TaskFault::Cancelled`, or `TaskFault::DoubleFaultFatal`).

#### Normative Rules for Structured Concurrency:
1. **Lifetime Containment Invariant**:
   For any scope $S$ and any child task $c \in \text{Children}(S)$:
   $$\mathop{\mathrm{Lifetime}}(c) \subseteq \mathop{\mathrm{Lifetime}}(S) \subset \mathop{\mathrm{Lifetime}}(\text{Frame}_{\text{parent}})$$
2. **Stack-Allocated Scope Invariant (Zero-Heap Fast Path)**:
   When a `scope` block is lexically enclosed within the calling activation frame:
   - **Intrusive Child-Stack Descriptors**: The parent `Scope` descriptor is allocated contiguously on the caller stack frame with $O(1)$ footprint (intrusive list head). Task tracking nodes (`TaskNode`) are allocated inline on each child fiber's own stack frame. Dynamic or static task fan-out requires zero dynamic heap allocation.
   - **Synchronous Scope Unwind-Barrier**: When an unwind occurs (due to parent frame panic or sibling task cancellation), the unwinder MUST NOT pop the stack frame hosting an active scope until all active child tasks reach terminal state (`Completed`, `Panicked`, or `Cancelled`), execute their `let scoped` LIFO cleanup handlers, and unlink from the scope descriptor (`active_count == 0`), strictly preventing stack-use-after-free hazards.
   - **Result Rendezvous Ownership**: Child return values $T$ reside within the quiescent child stack frame until moved out via `task.join()` or dropped during scope LIFO exit.
3. **Boundary Capability Confinement**: Passing active mutable capabilities (`&mut`, `&^mut`, `&{mut var}`) or live views across concurrent task boundaries is statically rejected (`E0601: CrossThreadDataRaceHazardError`).
4. **Concurrent Task Effect Confinement Invariant (`E0615`)**:
   For any concurrent child task $c$ spawned via `s.fork(task)` or data-parallel combinator (`Parallel::map`, `Parallel::fold`), the task callable $task$ MUST be closed under all user-defined algebraic effects:
   $$\mathop{\mathrm{Effects}}(task) \subseteq \{\text{Fiber}\} \quad \text{(or } \emptyset \text{ for pure/parallel combinators)}$$
   Every algebraic effect operation invoked within the execution tree of a concurrent child task MUST be intercepted and discharged by a local `with` handler lexically enclosed within that child task. Handlers established in parent or ancestor tasks MUST NOT be captured across concurrent task boundaries (`&closure`). Passing a callable carrying unhandled algebraic effects or capturing external effect handlers across a concurrent task boundary is statically rejected at compile time under `E0615: CrossTaskUnhandledEffectError`. Runtime-managed cooperative fiber scheduling operations (`eff Fiber`) are exempt.

```ril
use ril/concurrent::{scope, Scope, Task, TaskFault, PanicInfo, DoubleFaultInfo}

-- 1. Structured Concurrency and Task Panic Containment:
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

-- 2. Concurrency Safety: Rejecting live mutable view across task boundary
fn bad_concurrent_data_race() {
    let mut shared_data = [1, 2, 3]
    scope(\mut s -> {
        -- s.fork(\-> {                -- Error [E0601]: cannot capture mutable handle 'shared_data' across concurrent task boundary
        --     shared_data !> Array::push(4)
        -- })
        Ok()
    })
}

-- 3. Stack-Allocated Dynamic Fan-Out Invariant (Zero-Heap Fast Path):
fn batch_transform(items: []int) -> Result<[]int, TaskFault> @Concurrent {
    -- Invariant: parent Scope descriptor is allocated on caller stack (O(1)).
    -- Intrusive TaskNode tracking descriptors are allocated on respective child stacks.
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

-- 4. Concurrent Task Effect Confinement Invariant (E0615):
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

### 9.6 Data Parallelism (`Parallel::map`, `Parallel::fold`) & Deterministic Reductions

`ril/parallel` exports the `Parallel` namespace for evaluating data-parallel combinators across slice partitions. `Parallel::fold` requires chunk-local accumulators with local `&mut`, avoiding cross-core cache invalidation. Reductions merge intermediate results via a canonical binary tree ($G_{\text{canonical}} = 64$) guaranteeing bit-for-bit floating-point determinism.

```ril
use ril/parallel::Parallel

let numbers: []f64 = [1.1, 2.2, 3.3, 4.4, 5.5, 6.6, 7.7, 8.8]

-- 1. Pure Data-Parallel Mapping:
let scaled = numbers |> Parallel::map(\x -> x * 2.0)

-- 2. Floating-Point Deterministic Fold via Canonical Binary Reduction Tree (G_canonical = 64):
let total_sum = Parallel::fold(
    numbers,
    init_acc: \-> 0.0f64,
    fold_local: \mut acc, x -> { acc += x }, -- OK: thread-local &mut accumulator
    merge_acc: \a, b -> a + b
)

-- 3. Capability Confinement: Rejecting external mutable captures in parallel combinator
var external_counter = 0
-- let bad = numbers |> Parallel::map(\x -> {
--     external_counter += 1            -- Error [E0605]: cannot capture external mutable variable 'external_counter' in parallel combinator
--     x * 2.0
-- })
```

---

## 10. Compile-Time Computation & Totality

### 10.1 Static Type Values & Type Quotation (`type<T>`, `typeof`)

1. **Declarative Contexts**: Top-level type declarations and type annotations use direct type syntax without `type<...>`:

```ril
type User = { id: int }
let a: int = 10
let b: typeof a = 20                   -- OK: direct 'typeof' in type annotation
```

2. **Expression Contexts**: In type functions and expression positions, ALL types without exception MUST be enclosed in `type<...>`:

```ril
let t_int = type<int>                  -- OK: all types enclosed in type<...>
let t_inferred = type<typeof (1 + 2)>  -- OK: 'typeof' enclosed in type<...> in expression position
-- let bad_t = int                     -- Error [E0301]: bare type in expression context
-- let bad_inferred = typeof (1 + 2)   -- Error [E0301]: bare 'typeof' in expression context
```

3. **Type Functions & Invocation**: Unannotated type function parameters default to sort `Type` (`\T -> ...`). Type function application uses generic angle brackets `<...>`:

```ril
type Nullable = \T -> type<?T>
type PairOf = \T, U -> type<{ first: T, second: U }>

-- Applying type functions via '<...>':
type IntNullable = Nullable<int>          -- Resolves to ?int
type StringIntPair = PairOf<str, int>     -- Resolves to { first: str, second: int }

let value: IntNullable = Some(42)         -- OK: used as concrete type annotation
let pair: StringIntPair = .{ first: "id", second: 101 }
```

### 10.2 Pure Type Functions & Computation Model (`halt type`, `halt fn`)

1. **Return Invariant**: A type function is a compile-time pure function whose return expression MUST evaluate to a `type<T>`. Returning a non-type value raises `E0301`.
2. **Axiomatic Purity & Zero-Annotation Invariant**: Type functions evaluate strictly within the pure compile-time domain ($\mathbf{Eff} = \emptyset, \mathbf{Cap} = \emptyset$). They MUST NOT declare or carry algebraic effects (`@Effect`) or state capabilities (`&mut`, `&closure`, `&capture`, `&{ident}`) (`E0301`). Type function bodies enjoy unrestricted pure functional computation: local immutable bindings (`let`), conditionals (`if`), pattern matching (`match`), invocation of pure `meta fn` functions, pure collection combinators, and recursion.
3. **Totality Certification**: `halt type` certifies normal termination. Unmarked type functions operate under configurable compiler evaluation budgets (`E0811`).

```ril
-- 1. Meta helper function (compile-time pure calculation):
meta fn pad_align(size: int, align: int) -> int {
    (size + align - 1) & !(align - 1)
}

-- 2. Pure type function with control flow, meta computation, and type output:
halt type PaddedBuffer = \raw_size: int, T -> {
    let actual_size = pad_align(raw_size, 8)     -- OK: consumes meta fn and const value
    if actual_size > 1024 {
        type<{ heap_ptr: int, cap: int }>        -- Branch evaluates to type<T>
    } else {
        type<{ inline_data: []T, len: int }>     -- Branch evaluates to type<T>
    }
}

type FastBuf = PaddedBuffer<64, u8>              -- Resolves to { inline_data: []u8, len: int }

-- Static rejection of non-type return, effects, and capabilities:
-- type BadReturn = \T -> 42                     -- Error [E0301]: type function must evaluate to type<T>, found int
-- type BadEffect = \T -> type<T> @Async         -- Error [E0301]: type functions cannot declare algebraic effects
-- type BadCap = \T -> type<T> &closure          -- Error [E0301]: type functions cannot declare state capabilities

-- 3. Total Runtime Computation (halt fn):
halt fn total_clamp(val: int, min_val: int, max_val: int) -> int {
    if val < min_val { min_val }
    else if val > max_val { max_val }
    else { val }
}                                      -- OK: provably terminating runtime function

-- halt fn bad_loop(n: int) -> int {  -- Error [E0820]: 'halt fn' contains uncertified unbounded loop
--     while true {}
-- }
```

### 10.3 Disjoint Call Families & Evaluation Budgets

1. **Family Isolation**: Type functions can invoke `meta fn` callables and other type functions, but cannot invoke runtime `fn` callables (`E0810`).
2. **Runtime Isolation**: Runtime functions cannot invoke type functions (`E0810`).
3. **Budget Exhaustion**: Exceeding compiler evaluation limits halts compilation with `E0811`.

```ril
fn runtime_helper() -> int { 42 }

-- Type function cannot execute runtime function:
-- type BadStatic = \T -> {
--     let x = runtime_helper()        -- Error [E0810]: cannot invoke runtime function from compile-time type function
--     type<int>
-- }

-- Runtime function cannot invoke type function:
fn bad_runtime_fn() {
    -- let t = FastBuf<64, u8>         -- Error [E0810]: cannot invoke type function from runtime function
}

-- Compiler Evaluation Budget Exhaustion:
type RecursiveLoop = \T -> RecursiveLoop<T>
-- type Overflow = RecursiveLoop<int>  -- Error [E0811]: compile-time evaluation budget exceeded (max 100,000 steps)
```

### 10.4 Mapped Schemas & Type Introspection (`keyof`, Field Dot Projection `T.field`, `T.(K)`)

Type functions inspect and transform record schemas using `keyof`, dot field projection (`T.field` for static identifier lookup, `T.(expr)` for computed key projection), and mapped schema comprehensions (`{ [K in Expr]: TypeExpr }`):

```ebnf
TypeProjection   ::= PrimaryType "." ( Identifier | "(" Expression ")" )
MappedRecordType ::= "{" "[" Identifier "in" Expression "]" ":" TypeExpression "}"
```

1. **Schema Key Extraction (`keyof T`)**:
   - In type parameter bounds (`\K: keyof T`), `keyof T` enforces field membership.
   - In expression / meta contexts, `keyof T` evaluates to a compile-time immutable array `[]str`.
   - **Canonical Lexicographical Ordering**: `keyof T` is sorted strictly in UTF-8 byte order, ensuring Leibniz equivalence ($T_1 \equiv T_2 \implies \text{keyof } T_1 \equiv \text{keyof } T_2$).
2. **Field Dot Projection**: `T.field` statically projects field types. Computed projection `T.(expr)` evaluates any compile-time `str` expression against schema fields.
3. **Zero-Dialect Mapped Schema Comprehension (`{ [K in Expr]: TypeExpr }`)**:
   - `Expr` MUST evaluate to a compile-time known `[]str`.
   - `Identifier` binds the field name (of sort `str`) within the lexical scope of `TypeExpression`.
   - Key renaming and schema reshaping use ordinary pure expressions and helper functions; no dedicated keyword dialects (such as `as`) are admitted.

```ril
type User = { id: int, name: str, active: bool, secret_token: str }

-- 1. Schema Key Extraction (canonical []str in expression context):
meta let USER_KEYS: []str = keyof User
-- Resolves to: ["active", "id", "name", "secret_token"] (lexicographical order)

-- 2. Schema Field Dot Projection:
type IdType = User.id                  -- Resolves to int (static identifier projection)
type UserName = User.name              -- Resolves to str
-- type BadField = User.missing        -- Error [E0301]: field 'missing' does not exist in record 'User'

-- Nested schema dot projection:
type NestedConfig = { db: { host: str, port: int } }
type HostType = NestedConfig.db.host   -- Resolves to str

-- Dot projection on inferred record types:
let current_user = .{ id: 101, name: "Alice" }
type InferredId = typeof current_user.id          -- Resolves to int (value-level direct access)
type InferredName = (typeof current_user).name    -- Resolves to str (parenthesized type-level projection)

-- 3. Pick and Omit via standard array combinators:
type Omit = \T, Excluded: []str -> {
    let valid_keys = keyof T |> Array::filter(\k -> !(Excluded |> Array::contains(k)))
    type<{
        [K in valid_keys]: T.(K)
    }>
}

type Pick = \T, Included: []str -> {
    let valid_keys = keyof T |> Array::filter(\k -> Included |> Array::contains(k))
    type<{
        [K in valid_keys]: T.(K)
    }>
}

type PublicUser = Omit<User, ["secret_token"]>
-- Resolves to: { active: bool, id: int, name: str }

type UserCredentials = Pick<User, ["id", "name"]>
-- Resolves to: { id: int, name: str }

-- 4. Zero-Dialect Key Renaming (PrefixKeys via ordinary string expression):
type PrefixKeys = \T, prefix: str -> {
    let prefixed_keys = keyof T |> Array::map(\k -> prefix + "_" + k)
    type<{
        [K in prefixed_keys]: T.(str_strip_prefix(K, prefix + "_"))
    }>
}

type ApiUser = PrefixKeys<User, "api">
-- Resolves to: { api_active: bool, api_id: int, api_name: str, api_secret_token: str }

-- 5. Filtering by Field Value Type via first-class type equality (==):
type FilterByType = \T, TargetType -> {
    let matched_keys = keyof T |> Array::filter(\k -> type<T.(k)> == type<TargetType>)
    type<{
        [K in matched_keys]: T.(K)
    }>
}

type StringFields = FilterByType<User, str>
-- Resolves to: { name: str, secret_token: str }

-- 6. Pattern Matching over Field Types:
type FlexiblePatch = \T -> type<{
    [K in keyof T]: match type<T.(K)> {
        type<bool> -> bool,
        _          -> ?T.(K),
    }
}>

type UserPatch = FlexiblePatch<User>
-- Resolves to: { active: bool, id: ?int, name: ?str, secret_token: ?str }

let patch: UserPatch = .{ active: true, id: Some(1), name: None, secret_token: None }
```

### 10.5 Static Parameter Sorts & Adaptation Rules (`\param: Sort`)

Type functions accept four parameter sorts:

1. **Bare Types (`\T` or `\T: Type`)**: Accepts static type expressions. Unannotated parameters default to sort `Type`.
2. **Const Values (`\param: ValueType`)**: Accepts compile-time known constants (literals, `meta let`, statically foldable expressions). Passing runtime variables raises `E0810`.
3. **Bounded & Structural Types (`\T: { id: int, ..R }`, `\K: keyof T`)**: Enforces structural row subtyping and key inclusion.
4. **Higher-Kinded Constructors (`\M: Type -> Type`)**: Enforces constructor kind arity (`E0306`).
5. **Default Sort Arguments**: Type function parameters support default expressions conforming to their sort: `\T = u8`, `\cap: int = 1024`. Default arguments follow the Telescopic scoping and trailing rules (§3.11).

**Call-Site Interpretation**: In `TypeFunc<Arg1, Arg2>`, type parameter positions parse as `TypeExpression`; const value positions parse as compile-time expressions.

```ril
type WirePacket<version: int>(bytes)

let v1_packet: WirePacket<1> = WirePacket(b"\x01payload")
let v2_packet: WirePacket<2> = WirePacket(b"\x02payload_extended")

type SchemaV1 = { id: int, name: str }
type SchemaV2 = { id: int, name: str, email: str }

type VersionedSchema = \version: int -> match version {
    1 -> type<SchemaV1>,
    2 -> type<SchemaV2>,
    _ -> type<never>,
}

type ActivePayload = VersionedSchema<2> -- Resolves to SchemaV2
let user_v2: ActivePayload = .{ id: 10, name: "Alice", email: "alice@test.com" }

-- Structural constraint & keyof bound adaptation:
type PickField = \T: { ..R }, K: keyof T -> T.(K)
type UserName = PickField<SchemaV1, "name"> -- Resolves to str
-- type BadField = PickField<SchemaV1, "missing"> -- Error [E0301]: "missing" not in keyof SchemaV1

-- Higher-kinded constructor adaptation:
type Wrapper = \M: Type -> Type, T -> M<T>
type OptInt = Wrapper<Option, int>      -- Resolves to Option<int>
-- type BadKind = Wrapper<int, int>     -- Error [E0306]: KindMismatchError, expected Type -> Type, found int

-- Default arguments in pure type functions:
halt type PaddedRecord = \T: { ..R }, align: int = 8 -> type<{
    alignment: int,
    ..T,
}>
type DefaultPadded = PaddedRecord<SchemaV1>      -- OK: align defaults to 8
type CustomPadded = PaddedRecord<SchemaV1, 16>   -- OK: explicit override align = 16
```

### 10.6 Compile-Time Execution (`meta let`, `meta fn`) & Callable Introspection

`meta let` and `meta fn` execute strictly during compilation under deterministic totality budgets. Built-in reflection predicates (`is_pure`, `has_effect`, `has_capability`) inspect callables for purity, effects, and capabilities. Compile-time assertions reuse the standard prelude intrinsic `assert`, failing compilation with `E0830` (`MetaAssertionFailedError`) when breached. Conditional specialization reuses standard `if` branching over meta conditions without dedicated dialects.

**Phase Distinction & Cross-Stage Relaxation**:
Evaluation is divided into compile-time (meta stage) and runtime:
1. **Strict Compile-Time Closedness**: A `meta` context (`meta let`, `meta fn`) can only depend on and consume entities known at compile time (`meta` bindings, pure `meta fn` invocations, compile-time type values, and literals). Attempting to pass dynamic runtime values into a `meta` context or calling runtime functions from `meta` code is statically rejected (`E0810: CallFamilyViolationError`).
2. **Unidirectional Cross-Stage Relaxation**: Conversely, non-meta runtime contexts (`let`, `fn`) can freely consume `meta` bindings without restriction. Values produced by `meta` evaluation degrade monotonically into immutable constants and inlined immediates, representing a safe information-flow relaxation ($\text{Meta} \succ \text{Runtime}$).

```ril
-- 1. Meta Bindings & Compile-Time Functions:
meta let MAX_BUFFER_SIZE = 1024 * 64
meta fn compute_hash_mask(bits: int) -> int {
    (1 << bits) - 1
}
meta let CACHE_MASK = compute_hash_mask(8) -- Evaluated at compile-time: 255

-- Non-meta runtime function freely consumes meta binding (relaxation):
fn get_cache_slot(key: int) -> int {
    key & CACHE_MASK                       -- OK: CACHE_MASK is an inlined compile-time constant
}

-- 2. Callable Reflection Predicates:
fn pure_add(a: int, b: int) -> int { a + b }
fn effectful_log(s: str) -> () @Console { Console::print(s) }
fn mutating_sort(mut arr: []int) &mut { arr !> Array::sort() }

-- 'is_pure' asserts zero effects and zero parameter/external mutation:
meta let _ = assert(is_pure(pure_add), "pure_add must be mathematically pure")     -- OK
meta let _ = assert(!is_pure(effectful_log), "effectful_log is not pure")         -- OK
meta let _ = assert(!is_pure(mutating_sort), "mutating_sort is not pure")         -- OK

-- 'has_effect' and 'has_capability' inspect specific effects and capabilities:
meta let _ = assert(has_effect(effectful_log, @Console), "has @Console effect")   -- OK
meta let _ = assert(has_capability(mutating_sort, &mut), "requires &mut")        -- OK

-- Failed compile-time assertion halts compilation:
-- meta let _ = assert(is_pure(effectful_log), "audit check")
-- Error [E0830]: MetaAssertionFailedError: audit check (carries unhandled effect @Console)

-- 3. Zero-Dialect Static Specialization via Standard 'if':
fn dispatch_computation<F, T, R>(f: F, arg: T) -> R {
    meta let pure = is_pure(type<F>)
    if pure {
        f(arg)                         -- Compiler specializes: thread-safe, pure fast path
    } else {
        f(arg)                         -- Sequential, side-effect-aware path
    }
}
```

---

## 11. Modules, Program Execution & Prelude

### 11.1 Modules & Compilation Units

Every source file is an independent compilation unit. Compilation units are partitioned into two mutually exclusive kinds:

1. **Implementation Units (`.ril`)**: Standard modules containing executable definitions. Functions in `.ril` modules MUST provide implementation bodies (`{ ... }`).
2. **External Interface Declaration Units (`.d.ril`)**: Contract-only modules declaring external types, ambient constants, and foreign signatures without implementation bodies (§4.8). When a module path resolves to `<path>.d.ril`, the module is designated as an `ExternalContractModule` and linked to target-specific safe wrappers.

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
-- use math/geometry::{PI}              -- Error [E0201]: symbol 'PI' is private to module 'math/geometry'
```

### 11.2 Imports (`use`) & Visibility (`pub`)

```ebnf
UseDecl ::= [ "pub" ] "use" ModulePath [ "::" ( "{" ImportList "}" | "*" | Identifier ) ]
```

```ril
use ril/array::{push, pop}             -- Import specific items
pub use ril/math::*                    -- Re-export all public math items

fn calculate() {
    use ril/crypto::{sha256}           -- Block-scoped import: visible strictly inside calculate()
    let digest = sha256("data")
}
-- let bad = sha256("data")             -- Error [E0301]: unresolved identifier 'sha256'
```

### 11.3 Top-Level Initialization & Purity

Top-level declarations MUST be free of observable runtime side effects. Top-level mutable variables must be initialized with constant expressions.

```ril
let MAX_CONNECTIONS: int = 100
let DEFAULT_TITLE: str = "Ril Application"
var active_workers: int = 0            -- OK: initialized with constant expression

-- Prohibited top-level runtime side effects:
-- let current_time = Clock::now()      -- Error [E0202]: top-level declaration must be a pure constant expression
-- let db = Database::connect("db.loc") -- Error [E0202]: top-level declaration cannot invoke runtime I/O or effects
```

### 11.4 Unit Testing Blocks (`test`)

`test` blocks define isolated unit test suites. In production compilation modes, `test` blocks are completely eliminated from binary generation and carry zero runtime overhead.

```ril
test "array pushing and popping" {
    let mut items = [1, 2]
    items !> Array::push(3)
    assert(len(items) == 3, "expected 3 items")
}
```

### 11.5 Program Entry Point (`pub fn main`)

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

### 11.6 Standard Prelude Built-ins

The following types and functions are implicitly available in every compilation unit:

| Item | Kind | Description |
| :--- | :--- | :--- |
| `Option<T>`, `?T` | Sum Type | Optional value: `Some(T)` or `None` |
| `Result<T, E>` | Sum Type | Fallible operation outcome: `Ok(T)` or `Err(E)` |
| `[K: V]`, `Set<T>` | Types | Built-in associative map and unique set |
| `inner(wrapper)` | Function | Extracts underlying value from nominal wrapper `type W(T)` |
| `clone(x)` | Function | Allocates deep independent mutable duplicate of heap reference |
| `clone_immut(x)` | Function | Freezes heap object into permanently immutable `Immut<T>` |
| `derive(base, recipe)` | Function | Path-wise copy-on-write functional update over reference graph |
| `len(coll)` | Function | Returns element count of string, bytes, array, map, or set |
| `panic(msg)` | Function | Initiates deterministic runtime panic unwinding |
| `assert(cond, msg)` | Function | Verifies invariant; panics on breach |
| `print(s)`, `println(s)` | Functions | Writes text to standard output |

```ril
-- 1. Nominal Unwrapping via inner():
type UserId(int)
let uid = UserId(1001)
let raw_id: int = inner(uid)           -- 1001

-- 2. Deep Mutable Cloning via clone():
let mut original = [1, 2, 3]
let mut detached = clone(original)
detached !> Array::push(4)             -- Mutates 'detached'; 'original' remains [1, 2, 3]

-- 3. Permanent Immutability Freezing via clone_immut():
let frozen: Immut<[]int> = clone_immut(original)
-- frozen !> Array::push(5)            -- Error [E0520]: cannot mutate permanently immutable Immut<T>

-- 4. Functional Derivation via derive():
let base_cfg = .{ theme: "dark", retries: 3 }
let updated_cfg = base_cfg |> derive \mut next -> {
    next.theme = "light"
}
assert(base_cfg.theme == "dark" && updated_cfg.theme == "light")

-- 5. Length Inspection via len():
let count = len("hello")               -- 5 (Unicode scalar count)
let array_len = len([10, 20, 30])      -- 3

-- 6. Invariants and Panic Primitives:
assert(len(original) > 0, "must not be empty") -- OK
if len(original) == 0 {
    panic("unreachable state reached")  -- Initiates deterministic runtime panic
}
```

### 11.7 Anti-Fault Masking: Mandatory Inspection of `Result` (`E0720`)

To prevent silent bug propagation, Ril enforces the **Anti-Fault Masking Invariant**: any expression evaluating to `Result<T, E>` MUST be explicitly inspected, propagated, matched, or unpacked. Discarding a fallible `Result` without inspection is statically rejected (`E0720`).

```ril
fn save_profile(user_id: int) -> Result<(), str> {
    if user_id <= 0 { Err("invalid id") } else { Ok() }
}

fn process_request(id: int) -> Result<(), str> {
    -- Prohibited: discarding fallible Result without inspection
    -- save_profile(id)                 -- Error [E0720]: unused fallible Result must be handled

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

## 12. Diagnostic Error Codes Summary

| Code | Diagnostic Name | Normative Condition |
| :---: | :--- | :--- |
| **`E0101`** | `InvalidIdentifierCasingError` | Identifier casing style violates grammatical role requirement |
| **`E0102`** | `MalformedIdentifierSyntaxError` | Identifier contains illegal consecutive/trailing underscores or unnormalized acronym casing |
| **`E0103`** | `PatternCasingCollisionError` | Pattern binding position contains illegal casing causing semantic collision |
| **`E0201`** | `PrivateItemAccessError` | Accessing or importing unexported private module symbol |
| **`E0202`** | `TopLevelSideEffectError` | Top-level declaration contains non-constant runtime side effects |
| **`E0203`** | `DuplicateDeclarationError` | Redeclaring an existing identifier in the same scope |
| **`E0301`** | `TypeMismatchError` | Expression type incompatible with expected type |
| **`E0302`** | `UnexpectedFieldError` | Closed record supplied with undeclared fields |
| **`E0305`** | `NominalTypeMismatchError` | Mismatched nominal type wrapper identities |
| **`E0306`** | `KindMismatchError` | Mismatched higher-kinded type constructor or sort constraint |
| **`E0308`** | `OpaqueBoundaryViolationError` | Attempting to unpack, penetrate with `inner()`, or pattern deconstruct an opaque type externally |
| **`E0309`** | `VacuousBindingError` | 'let' pattern binds zero variables (excluding explicit wildcard discard 'let _ = expr') |
| **`E0310`** | `InvalidatedNarrowingAccessError` | Accessing identifier whose flow narrowing was invalidated by reassignment or mutation |
| **`E0311`** | `ContradictoryNarrowingError` | Narrowing predicate is statically unsatisfiable under active flow environment |
| **`E0313`** | `CyclicTypeAliasError` | Structural type aliases form a cyclic dependency without nominal or sum indirection |
| **`E0315`** | `EscapingLocalNominalTypeError` | Local nominal wrapper or sum type escapes enclosing function boundary as return type |
| **`E0316`** | `NonTrailingDefaultGenericParamError` | Generic parameter without default follows generic parameter with default |
| **`E0317`** | `FunctionDefaultGenericProhibitedError` | Function generic parameter declares default type or value argument |
| **`E0320`** | `ForwardTypeDefaultReferenceError` | Generic default parameter expression contains forward reference or circular dependency |
| **`E0323`** | `ConstGenericSortMismatchError` | Const generic argument does not match expected parameter sort |
| **`E0401`** | `ValueTypeMutableBorrowError` | Attempt to declare or pass a value type as `mut` parameter |
| **`E0402`** | `ValueTypePinnedMutError` | Attempting to declare a value type as pinned mutable handle `let mut` |
| **`E0403`** | `VarParameterProhibitedError` | Attempting to declare a function parameter with `var` |
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
| **`E0601`** | `CrossThreadDataRaceHazardError` | Passing live mutable view across concurrent task boundary |
| **`E0605`** | `InvalidParallelCapabilityError` | Capturing external mutable capabilities in parallel combinator |
| **`E0607`** | `DerivedProxyEscapeError` | Derived proxy escapes 'derive' recipe via return, assignment, or closure publication |
| **`E0610`** | `DuplicateResumeInvocationError` | Invoking affine one-shot resumption `resume` more than once |
| **`E0611`** | `EscapingResumeError` | Escaping resumption handle beyond handler arm lexical scope |
| **`E0612`** | `UnhandledEffectError` | Invoking effect operation without in-scope handler or declaring effect in callable signature |
| **`E0614`** | `EscapingEffectClosureError` | Closure with unhandled effect escaping to heap record without in-scope handler |
| **`E0615`** | `CrossTaskUnhandledEffectError` | Passing callable with unhandled effect or external effect handler across concurrent task boundary |
| **`E0616`** | `ScopedCleanupEffectError` | Resource cleanup handler (`on_close`) declares or invokes unhandled algebraic effects |
| **`E0617`** | `ScopedCleanupDivergenceError` | Resource cleanup handler (`on_close`) declares or invokes divergent operations (`@Div`) |
| **`E0618`** | `UndischargedLocalEffectError` | Local algebraic effect declared in 'where' is not completely discharged within enclosing block |
| **`E0701`** | `ChainedAssignmentProhibitedError` | Chaining assignments (`a = b = c`) |
| **`E0702`** | `InvalidWhereItemError` | Declaring variable binding or non-hoistable item in `where` clause |
| **`E0703`** | `IllegalSequentialDeclarationError` | Declaring 'fn', 'type', or 'eff' in sequential statement stream instead of 'where' clause |
| **`E0704`** | `InvalidSignatureWhereItemError` | Declaring 'fn' or 'eff' in signature 'where' clause (signature where is restricted to 'type') |
| **`E0705`** | `DownwardScopeReferenceError` | Signature 'where' clause references item declared in inner block 'where' clause |
| **`E0706`** | `SignatureTypeNotInWaistWhereError` | Function signature references type declared in block 'where' clause instead of signature 'where' clause |
| **`E0710`** | `IllegalControlTransferInFallbackError` | Embedding `return`/`last` in fallback operator `??` |
| **`E0711`** | `InvalidResultFallbackError` | Supplying raw value fallback for `Result` without error closure |
| **`E0720`** | `UnusedFallibleResultError` | Discarding fallible `Result` without inspection |
| **`E0810`** | `CallFamilyViolationError` | Crossing disjoint runtime `fn` and compile-time `meta`/`type` call families |
| **`E0811`** | `CompileTimeBudgetExceededError` | Exhausting compiler evaluation step budget in meta/type functions |
| **`E0820`** | `TotalityViolationError` | Totality certification failed in `halt fn` (unbounded recursion/loop) |
| **`E0830`** | `MetaAssertionFailedError` | Compile-time `assert` condition evaluated to `false` in `meta` context |
| **`E0901`** | `BodyInDeclModuleError` | Supplying an implementation body, variable initializer, or mutable binding in a '.d.ril' declaration unit |
| **`E0902`** | `MissingBodyInStandardModuleError` | Omitting an implementation body from a function declared in a standard '.ril' module |
| **`E0907`** | `ForeignStructuralFieldPenetrationError` | Attempting to access fields, mutate, index, deconstruct, or instantiate an opaque external type |
