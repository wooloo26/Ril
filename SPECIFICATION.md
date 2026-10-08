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
4. **Boundary Containment**: In concurrent execution, child task panics are isolated at structured concurrency boundaries (`nursery`), resolving to `Result<T, TaskFault>` (`TaskFault::Panicked`).

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

-- 4. Boundary Containment: child panics isolated at structured nursery boundary
use ril/concurrent::{nursery, TaskFault}

let nursery_outcome: Result<int, TaskFault> = nursery(\mut scope -> {
    scope.spawn(\-> { panic("worker failure") })
    Ok(42)
})
-- nursery_outcome evaluates to Err(TaskFault::Panicked(...))
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

### 2.4 Identifiers

```ebnf
Identifier         ::= ( UnicodeLetter { IdentifierContinue } )
                     | ( "_" IdentifierContinue { IdentifierContinue } )
IdentifierStart    ::= "_" | UnicodeLetter
IdentifierContinue ::= UnicodeLetter | Digit | "_"
```

Identifiers use `PascalCase` for types, constructors, and effects; `snake_case` for variables, functions, and fields. A single underscore `_` is the wildcard pattern, not an identifier.

```ril
let user_count = 10                    -- OK: variable identifier
type UserAccount = { id: int }         -- OK: type identifier
effect FileIo = { read: fn() -> str }  -- OK: effect identifier
let _ = user_count                     -- OK: wildcard discard
```

### 2.5 Keywords

The following 31 tokens are strictly reserved keywords:

```
as       break    continue effect   else
false    fn       for      if       in
infer    is       keyof    let      loop
match    meta     module   mut      never
opaque   pub      return   test     true
type     typeof   use      where    while
with
```

Contextual keywords (`scoped`, `view`, `lacks`, `halt`, `resume`) have syntactic roles only in specific grammar positions:

```ril
-- Reserved keywords in action:
pub opaque type Token = int            -- 'pub', 'opaque', 'type'
meta let COMPILE_ID = 101              -- 'meta', 'let'
effect Logger = { log: fn(str) -> () } -- 'effect', 'fn'
use ril/array::{push}                  -- 'use'

fn calculate(val: ?int) -> int {       -- 'fn'
    let bound = match val {            -- 'let', 'match'
        Some(x) if x > 0 -> x,         -- 'if'
        _ -> 0,
    }
    let is_positive = bound is 1..=10  -- 'is'
    let mut sum = 0                    -- 'mut'
    for n in [1, 2, 3] {               -- 'for', 'in'
        if sum > 10 { break }          -- 'break'
        else { continue }              -- 'else', 'continue'
    }
    while false { loop {} }            -- 'while', 'false', 'loop'
    bound                              -- tail expression
where                                  -- 'where' inside block
    type Dummy = never                 -- 'never'
}

-- Contextual keywords in action:
let scoped res = File::open("a.txt")?  -- 'scoped' in let binding
let view v = res                       -- 'view' in handle binding
halt fn total_step() -> bool { true }  -- 'halt', 'true'
with Logger::log(msg) -> resume(())    -- 'with', 'resume' (statement-level handler)
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
let mut b = a                          -- Independent copy
b += 1                                 -- Modifies 'b'; 'a' remains 42
assert(a == 42 && b == 43)

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

### 3.3 Record Types & Open Rows

Records are structural collections of named fields. Closed records do not support width subtyping. Open rows (`..`) allow accepting records with additional fields.

```ebnf
RecordType  ::= "{" [ RecordField { "," RecordField } [ "," ] [ ".." [ Identifier ] ] ] "}"
RecordField ::= [ "mut" ] Identifier ":" TypeExpression
```

```ril
type User = { id: int, name: str }
let u: User = .{ id: 1, name: "Alice" } -- OK: exact closed record match

-- Closed record rejects extra fields (E0302):
-- let bad_u: User = .{ id: 1, name: "Alice", age: 30 } -- Error [E0302]: unexpected field 'age' in closed record 'User'

-- Open row acceptance and rejection:
fn get_id(r: { id: int, .. }) -> int {
    r.id
}
let id1 = get_id(u)                    -- OK: User satisfies { id: int, .. }
let id2 = get_id(.{ id: 2, age: 25 })  -- OK: extra field 'age' accepted by '..'
-- let bad_id = get_id(.{ age: 25 })   -- Error [E0301]: missing required field 'id' in open row

-- Named row tail polymorphism:
fn with_timestamp<R>(r: { ..R }) -> { timestamp: int, ..R } {
    .{ timestamp: 1600000000, ..r }
}
let stamped = with_timestamp(.{ id: 1, tag: "audit" })
assert(stamped.tag == "audit" && stamped.timestamp == 1600000000)
```

### 3.4 Array, Map & Set Types

```ebnf
ArrayType ::= "[]" TypeExpression
MapType   ::= "Map" "<" TypeExpression "," TypeExpression ">"
SetType   ::= "Set" "<" TypeExpression ">"
TupleType ::= "(" TypeExpression "," { TypeExpression "," } [ TypeExpression ] ")"
```

```ril
let numbers: []int = [1, 2, 3]         -- Type: []int
let coords: (int, int) = (10, 20)      -- Type: (int, int)
let config: Map<str, str> = Map::new() -- Type: Map<str, str>
let visited: Set<int> = Set::new()     -- Type: Set<int>
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

### 3.6 Nominal Type Wrappers

Nominal wrappers encapsulate an underlying type into an isolated nominal identity with zero runtime overhead.

```ebnf
NominalDecl   ::= [ "pub" ] "type" Identifier [ GenericParams ] "(" NominalFields ")" [ WhereClause ]
NominalFields ::= VariantField { "," VariantField } [ "," ]
```

```ril
type UserId(int)
type AccountId(int)
type Point2D(x: f64, y: f64)           -- Multi-field nominal wrapper

let uid = UserId(1001)
let aid = AccountId(1001)
let pt = Point2D(10.0, 20.0)

-- uid == aid                          -- Error [E0305]: mismatched nominal types 'UserId' and 'AccountId'
let raw_id: int = inner(uid)           -- OK: unwrap single-element nominal wrapper via prelude 'inner()'
let UserId(unwrapped_id) = uid         -- OK: pattern-matching unwrap
let Point2D(x, y) = pt                 -- OK: multi-field pattern unwrap
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

1. **Handle-Level Read-Only Invariant**: Immutability is enforced at the variable binding and handle level. A binding declared with `let` grants read-only access.
2. **Live Views (`let view x = obj`)**: A live view strips write permissions locally but observes concurrent or subsequent mutations on the underlying heap object.
3. **Definite Mutation Invariant**: Any binding declared with `let mut` or parameter declared with `mut` MUST undergo at least one reachable write operation along an executable path.

```ril
type Counter = { mut count: int }
let mut original = Counter.{ count: 0 }

let view v = original                  -- Live view into 'original'
-- v.count = 5                         -- Error [E0520]: cannot mutate through read-only view 'v'

original.count += 1
let observed = v.count                 -- observed is 1 (live view reflects mutation)

let mut unused_mut = 42                -- Error [E0527]: variable 'unused_mut' declared 'let mut' but never modified
```

### 3.10 Copy-on-Write Deep Updates (`produce`) & Ownership Transfer (`move`)

1. **`produce(base, recipe)`**: Executes deep functional updates over reference data graphs via copy-on-write proxy mechanics. The mutating closure `recipe` mutates a draft proxy in place, returning a fresh, unaliased immutable object without modifying `base`. Draft proxies cannot escape the recipe closure (`E0607`).
2. **`move(x)`**: Transfers unaliased ownership across concurrency or lexical boundaries, affinely invalidating the local handle `x`.

```ril
type UserProfile = { mut name: str, mut settings: { mut theme: str } }

let u1 = UserProfile.{ name: "Alice", settings: .{ theme: "dark" } }

-- Functional update via produce:
let u2 = u1 |> produce \mut draft -> {
    draft.settings.theme = "light"     -- In-place mutation on draft proxy
}
assert(u1.settings.theme == "dark")    -- u1 remains unchanged
assert(u2.settings.theme == "light")   -- u2 is a fresh updated copy

-- Draft proxy escape is strictly prohibited:
-- let escaped = u1 |> produce \mut draft -> draft -- Error [E0607]: draft proxy cannot escape 'produce' closure

-- Affine ownership transfer:
let u3 = move(u2)                      -- 'u2' is moved to 'u3'
-- let bad = u2.name                   -- Error [E0606]: use of moved value 'u2'
-- let double_move = move(u2)          -- Error [E0606]: use of moved value 'u2'
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

### 4.2 Mutable Bindings (`let mut`)

```ebnf
LetMutDecl ::= "let" "mut" Identifier [ ":" TypeExpression ] "=" Expression
```

```ril
let mut counter = 0
counter += 1                           -- OK: mutable binding reassignment

-- Pattern-level mutable destructuring:
let (mut start, mut end) = (0, 10)
start += 1; end -= 1                   -- OK: individual fields mutated

-- Definite Mutation Invariant:
-- let mut unused = 100                -- Error [E0527]: variable 'unused' declared 'let mut' but never modified
```

### 4.3 Scoped Resource Bindings (`let scoped`, `let scoped mut`)

Scoped bindings associate resources with lexical scopes. When exiting the enclosing scope (by normal completion, return, or unwinding), the cleanup handler executes in strict Last-In, First-Out (LIFO) order.

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
    -- 'let scoped mut' permits in-place mutation of the scoped handle:
    let scoped mut second = Resource.{
        name: "R2",
        on_close: \-> event_log !> Array::push("closed_R2")
    }
    second.name = "R2_modified"        -- OK: 'second' is declared 'let scoped mut'

    -- Scope exit triggers cleanup in strict LIFO order:
    -- 'second' closes FIRST, 'first' closes SECOND
}
assert(event_log == ["closed_R2", "closed_R1"])

-- Iteration cleanup executes at the end of each iteration:
let mut iter_log: []str = []
for item in ["A", "B"] {
    let scoped res = Resource.{
        name: item,
        on_close: \-> iter_log !> Array::push("closed_" ++ item)
    }
    -- 'res' is cleaned up immediately before the next iteration begins
}
assert(iter_log == ["closed_A", "closed_B"])
```

### 4.4 Live View Bindings (`let view`)

An explicit `let view` binding creates a live read-only observation handle into an existing reference object located on the managed GC heap. It strips write permissions locally while dynamically observing mutations performed through the underlying mutable root.

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
-- observer.val = 20                   -- Error [E0520]: cannot mutate through read-only view 'observer'

-- Mutations to the underlying object are dynamically observed through the view:
original.val = 42
assert(observer.val == 42)             -- OK: live view reflects mutation

-- Concurrency Invariant:
-- A live mutable view cannot escape across a concurrent task boundary:
-- nursery.spawn(\-> observer.val)     -- Error [E0601]: cannot pass live mutable view across task boundary
```

### 4.5 Type Declarations & Opaque Types

```ebnf
TypeDecl       ::= [ "pub" ] [ "halt" ] "type" Identifier [ GenericParams ] [ WhereClause ] "=" TypeExpression
OpaqueTypeDecl ::= [ "pub" ] "opaque" "type" Identifier [ GenericParams ] [ WhereClause ] "=" TypeExpression
```

```ril
module App;
pub opaque type SessionToken = str     -- Opaque type representation is hidden across module boundaries

-- Inside module 'App': SessionToken can be constructed from str:
pub fn create_token(raw: str) -> SessionToken {
    raw                                -- OK: internal module code can access underlying type
}

-- In external client module:
-- use App::{SessionToken, create_token};
-- let token: SessionToken = "raw"     -- Error [E0301]: expected opaque 'SessionToken', found 'str'
-- let s: str = token                  -- Error [E0301]: cannot implicitly convert opaque 'SessionToken' to 'str'

-- Existential opaque type witness in record:
type Serializer<T> = {
    opaque type WireFormat,
    encode: fn(T) -> WireFormat,
    decode: fn(WireFormat) -> T,
}
let int_serializer: Serializer<int> = .{
    type WireFormat = str,
    encode: \n -> "{n}",
    decode: \s -> Int::parse(s).unwrap(),
}
```

### 4.6 Effect Declarations

```ebnf
EffectDecl   ::= [ "pub" ] "effect" Identifier [ GenericParams ] "=" "{" EffectOpDecl { "," EffectOpDecl } [ "," ] "}"
               | [ "pub" ] "effect" Identifier [ GenericParams ] "=" "{" Identifier { "," Identifier } [ "," ] "}"
EffectOpDecl ::= Identifier ":" FunctionType
```

```ril
effect Console = {
    print: fn(str) -> (),
    read_line: fn() -> str,
}

effect State<S> = {
    get: fn() -> S,
    put: fn(S) -> (),
}

effect AppEffects = { Console, State<int> } -- Combined effect set
```

---

## 5. Expressions & Operators

### 5.1 Operator Precedence & Associativity

| Level | Operators | Associativity | Description |
| :---: | :--- | :---: | :--- |
| **1** | `.` `?.` `?[` `[]` `()` `::` postfix `?` | Left | Member access, safe navigation, indexing, invocation, postfix `?` |
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
let mut x = 10
x = 20                                 -- Simple assignment
x += 5                                 -- Compound addition (25)
x -= 2                                 -- Compound subtraction (23)
x *= 2                                 -- Compound multiplication (46)
x /= 2                                 -- Compound division (23)
x %= 5                                 -- Compound remainder (3)

-- Compound wrapping arithmetic:
let mut byte_val: u8 = 250u8
byte_val +%= 10u8                      -- 4u8 (compound wrapping addition)
byte_val -%= 10u8                      -- 250u8 (compound wrapping subtraction)
byte_val *%= 2u8                       -- 244u8 (compound wrapping multiplication)

-- Compound bitwise assignments:
let mut flags = 0b0011
flags |= 0b1100                        -- 0b1111
flags &= 0b1010                        -- 0b1010
flags ^= 0b0011                        -- 0b1001
flags <<= 1                            -- 0b10010
flags >>= 2                            -- 0b00100

-- Chained assignment is prohibited:
-- x = y = 10                          -- Error [E0701]: assignment chaining is prohibited
```

---

## 6. Control Flow & Pattern Matching

### 6.1 Block Expressions, Tail Values & Hoisted `where` Declarations

A block `{ ... }` evaluates to its tail expression. A block may conclude with a trailing `where` clause declaring mutually recursive helper functions (`fn`) and local types (`type`). Because functions and types are purely declarative with no sequential initialization side effects, they are hoisted across the entire block scope. Variable bindings (`let`, `let mut`) carry sequential side effects and are strictly prohibited in `where` (`E0702`).

```ebnf
Block       ::= "{" [ StatementList ] [ Expression ] [ WhereClause ] "}"
WhereClause ::= "where" WhereItem { Separator WhereItem }
WhereItem   ::= FunctionDecl | TypeDecl
```

```ril
let total = {
    let base = compute_base()
    let parity = is_even(base)
    base
where
    fn compute_base() -> int { 100 }
    fn is_even(n: int) -> bool { if n == 0 { true } else { is_odd(n - 1) } }
    fn is_odd(n: int) -> bool { if n == 0 { false } else { is_even(n - 1) } }
}

-- Types and functions can be mutually declared in 'where':
let user_summary = {
    let u: LocalUser = .{ id: 1, name: "Alice" }
    format_user(u)
where
    type LocalUser = { id: int, name: str }
    fn format_user(u: LocalUser) -> str { u.name ++ "#" ++ Int::to_str(u.id) }
}

-- Prohibited: variable bindings cannot be declared in 'where' (only 'fn' and 'type' permitted):
-- let bad = {
--     base + offset
-- where
--     fn compute() -> int { 10 }
--     let offset = 25                  -- Error [E0702]: InvalidWhereItemError: variable bindings cannot be declared in 'where' clause
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
-- 1. 'loop' with 'break' yielding a value:
let mut i = 0
let found = loop {
    i += 1
    if i == 5 { continue }             -- OK: skips to next iteration
    if i == 10 { break i * 2 }         -- Loop evaluates to 20
}

-- 2. 'while' loop:
while i > 0 {
    i -= 1
}

-- 3. 'for' loop over ranges and collections:
let mut sum = 0
for x in 1..=5 {
    if x % 2 == 0 { continue }         -- 'continue' skips even numbers
    sum += x
}
assert(sum == 9)                       -- 1 + 3 + 5
```

### 6.4 Control Transfers (`break`, `continue`, `return`)

```ril
fn search(matrix: [][]int, target: int) -> bool {
    for row in matrix {
        for cell in row {
            if cell == target { return true }
        }
    }
    false
}
```

### 6.5 Guarded Bindings (`let ... else`)

`let Pattern = expr else { Block }` matches a pattern or diverges. The `else` block MUST diverge (evaluate to `never`).

```ril
fn process_account(data: Map<str, str>) -> Result<str, str> {
    -- The 'else' block MUST diverge (evaluate to 'never'):
    let Some(id) = data["account_id"] else {
        return Err("missing account_id") -- OK: diverges via 'return'
    }

    -- Non-diverging 'else' is statically rejected:
    -- let Some(name) = data["name"] else {
    --     println("name missing")     -- Error [E0301]: 'else' branch of 'let ... else' must diverge
    -- }

    Ok(id)
}

-- Divergence via 'continue' and 'break' inside loops:
for entry in records {
    let Ok(val) = parse_entry(entry) else {
        continue                       -- OK: diverges out of this iteration
    }
    process(val)
}
```

### 6.6 Pattern Matching (`match`)

```ebnf
MatchExpr     ::= "match" Expression "{" [ MatchArm { "," MatchArm } [ "," ] ] "}"
MatchArm      ::= Pattern [ "if" Expression ] "->" Expression
Pattern       ::= OrPattern
OrPattern     ::= GuardPattern { "|" GuardPattern }
GuardPattern  ::= SinglePattern [ "if" Expression ]
SinglePattern ::= LiteralPattern | VariablePattern | WildcardPattern
                | TuplePattern | RecordPattern | ConstructorPattern | RangePattern
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
```

---

## 7. Functions, Closures & Callables

### 7.1 Named Function Declarations & Contrast Matrix

Named functions are declared at module or block scope. They support newspaper ordering (module-wide hoisting) and mutual recursion without forward declarations.

```ebnf
FunctionDecl      ::= [ "pub" ] [ "halt" ] "fn" Identifier [ GenericParams ]
                      "(" [ ParameterList ] ")" [ ReturnType ] [ EffectAnnot ] [ StateAnnot ]
                      [ WhereClause ] Block
ParameterList     ::= Parameter { "," Parameter } [ "," ]
Parameter         ::= [ "mut" ] Identifier [ ":" TypeExpression ] [ "=" Expression ]

Argument          ::= [ Identifier ":" ] ( "mut" AssignTarget | Expression )
ArgumentList      ::= Argument { "," Argument } [ "," ]
CallExpr          ::= Expression "(" [ ArgumentList ] ")" [ TrailingClosure ]
TrailingClosure   ::= AnonFnExpr
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
| **Handle Requirement** | Direct call / `let` handle | Callable via `let` handle | `let` (read-only capture) or `let mut` (mut capture) |

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
-- add_score(mut frozen_player, 5)     -- Error [E0527]: cannot borrow read-only handle 'frozen_player' as 'mut'
-- fn bad_inc(mut count: int) &mut {}  -- Error [E0401]: value types (int) cannot be declared as 'mut' parameters
-- fn noop_mut(mut u: User) &mut {}    -- Error [E0527]: 'mut' parameter 'u' declared but never modified
```

#### Default Parameters and Named Arguments

1. Default expressions MUST be pure expressions (zero unhandled effects, zero state mutations).
2. Mutable parameters (`mut param: T`) CANNOT declare default values.
3. Explicit arguments evaluate strictly left-to-right before omitted defaults.
4. Named arguments allow order-independent binding at call sites.

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
```

### 7.3 Anonymous Functions, Trailing Closures & Field Accessors

```ebnf
AnonFnExpr   ::= "\" [ AnonParams ] "->" ( Expression | Block )
AnonParams   ::= AnonParam { "," AnonParam } [ "," ]
AnonParam    ::= [ "mut" ] Identifier [ ":" TypeExpression ]
AccessorExpr ::= "\" "." Identifier { "." Identifier }
```

```ril
-- 1. Standard Anonymous Functions:
let double = \x -> x * 2
let sum = [1, 2, 3] |> Array::fold(0, \acc, x -> acc + x)

-- 2. Trailing Closure Syntax:
let doubled = [1, 2, 3] |> Array::map \x -> x * 2

fn run_job(f: fn() -> int) -> int { f() }
let job_res = run_job \-> 42

-- 3. Shorthand Field Projection Accessors (\.field):
type Employee = { id: int, name: str, salary: int }
let employees = [
    Employee.{ id: 1, name: "Alice", salary: 8000 },
    Employee.{ id: 2, name: "Bob", salary: 6000 },
]

let names = employees |> Array::map(\.name)       -- Evaluates to ["Alice", "Bob"]
let salaries = employees |> Array::map(\.salary)   -- Evaluates to [8000, 6000]
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
    let mut total = start
    \step -> {
        total += step
        total
    }                                  -- Captures mutable local 'total'
}

let mut acc = make_accumulator(100)    -- Requires 'let mut acc'
let a1 = acc(20)                       -- 120: valid invocation through 'let mut' handle

let frozen_acc = make_accumulator(10)
-- frozen_acc(5)                       -- Error [E0520]: cannot invoke mutable-capturing closure via read-only handle 'frozen_acc'

-- Nested Closures and Flat Chain Elaboration:
fn make_nested_multiplier(factor: int) -> (fn(int) -> (fn(int) -> int &closure) &closure) &capture {
    let mut base_multiplier = factor
    \multiplier_step -> {
        let mut intermediate = base_multiplier * multiplier_step
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
effect Logger = { log: fn(str) -> () }
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

-- 4. External State Capability Forwarding (&{mut var}):
let mut GLOBAL_TOTAL = 0
fn add_to_global(n: int) -> int &{mut GLOBAL_TOTAL} {
    GLOBAL_TOTAL += n
    GLOBAL_TOTAL
}

fn execute_global_step() -> int &{mut GLOBAL_TOTAL} {
    apply(10, add_to_global)           -- Call site transparently inherits &{mut GLOBAL_TOTAL}
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
    let mut total = 0
    let mut i = 1
    while i <= n {
        total += i
        i += 1
    }
    total                              -- Pure to callers: signature is fn(int) -> int
}

-- 2. Local Capability Discharge with reference types and &mut callees:
fn generate_sequence(count: int) -> []int {
    let mut local_buf = Buffer.{ items: [] }
    let mut i = 0
    while i < count {
        append_val(mut local_buf, i)   -- &mut discharged locally: local_buf does not escape
        i += 1
    }
    local_buf.items                    -- Pure: signature carries NO &mut!
}

-- 3. Local Discharge of Retained Sharing (&^mut):
type NodeHub = { mut nodes: []int }
fn link(mut hub: NodeHub, mut node: int) &^mut { hub.nodes !> Array::push(node) }

fn test_internal_hub() -> int {
    let mut local_hub = NodeHub.{ nodes: [] }
    let mut local_node = 42
    link(mut local_hub, mut local_node) -- &^mut discharged locally: all origins frame-confined
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

### 8.3 Retained Mutable Sharing (`&^mut`, `&{^mut var}`)

Retained mutable sharing occurs when execution creates a persistent writable access path that survives the call or closure publication boundary ($\ge 2$ independent surviving write paths).

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

-- 3. External Named Retained Mutable Sharing (&{^mut var}):
-- Stashes a mutable parameter into an external global container
let mut GLOBAL_HUB = Hub.{ entries: [] }

fn publish_entry(mut e: Entry) &{^mut GLOBAL_HUB} {
    GLOBAL_HUB.entries !> Array::push(e) -- Survives call: 'e' is retained in GLOBAL_HUB
}

-- 4. Returning a closure that captures and shares external mutable state:
let mut ACTIVE_CONNECTIONS = 0

fn make_connection_ticker() -> (fn() -> int &{mut ACTIVE_CONNECTIONS}) &{^mut ACTIVE_CONNECTIONS} {
    \-> {
        ACTIVE_CONNECTIONS += 1
        ACTIVE_CONNECTIONS
    }
}

-- Covariant subsumption across capability lattice:
type Retainer = fn(mut Hub, mut Entry) &^mut
let f_retain: Retainer = register_entry -- Exact match
let f_touch: Retainer = \mut h, mut e -> { e.id += 1 } -- OK: &mut subsumed by &^mut
```

### 8.4 External State Tracking (`&{var}`, `&{mut var}`, `&{^mut var}`)

Accessing module-level or outer lexical bindings without passing them as parameters requires explicit named capability annotations:

```ril
let APP_CONFIG_NAME = "Production"
let mut TRANSACTION_COUNT = 0

-- 1. Read-only external access:
fn get_config_name() -> str &{APP_CONFIG_NAME} {
    APP_CONFIG_NAME                    -- OK: declared &{APP_CONFIG_NAME}
}

-- 2. Mutable external access:
fn record_transaction() -> () &{mut TRANSACTION_COUNT} {
    TRANSACTION_COUNT += 1             -- OK: declared &{mut TRANSACTION_COUNT}
}

-- 3. Static errors on missing annotations:
-- fn bad_read() -> str { APP_CONFIG_NAME }          -- Error [E0510]: missing capability '&{APP_CONFIG_NAME}'
-- fn bad_write() { TRANSACTION_COUNT += 1 }        -- Error [E0510]: missing capability '&{mut TRANSACTION_COUNT}'

-- 4. Prohibition of Anonymous Concealment:
-- fn conceal_write() &mut { TRANSACTION_COUNT += 1 } -- Error [E0510]: cannot use anonymous '&mut' to conceal external 'TRANSACTION_COUNT'
```

### 8.5 Closure Capabilities & Handle Invocation Permissions

Invoking a closure that captured **mutable state** strictly requires the handle to be bound as `let mut` or passed as a `mut` parameter. Calling through a read-only `let` handle triggers `Error [E0520]`. Invoking a closure with **read-only** captures requires only `let`.

```ril
-- Mutable-capturing closure:
fn create_counter(start: int) -> (fn() -> int &closure) &capture {
    let mut count = start
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

-- E0520: MutabilityLaunderingError (binding read-only to let mut or mutating through view)
let doc = UserDoc.{ title: "Draft", score: 0 }
-- doc.score = 10                      -- Error [E0520]: cannot mutate field through read-only handle 'doc'
-- let mut laundered = doc             -- Error [E0520]: cannot bind read-only handle to 'let mut'

-- E0521: DestructureMutabilityLaunderingError (destructuring read-only into mut fields)
-- let { mut score } = doc             -- Error [E0521]: cannot bind read-only field to 'mut' pattern

-- E0522: ContainerMutabilityLaunderingError (injecting read-only reference into mutable container)
let mut doc_list: []UserDoc = []
-- doc_list !> Array::push(doc)        -- Error [E0522]: cannot store read-only reference 'doc' into mutable array
let detached = doc |> clone            -- OK: clone() produces independent detached mutable duplicate
doc_list !> Array::push(detached)      -- OK

-- E0523 & E0524: Mut-Mut and Read-Mut aliasing hazards (see §8.6)

-- E0525: SpreadLaunderingError (shallow-spreading read-only record into let mut root)
-- let mut spread_doc = UserDoc.{ ..doc, score: 99 } -- Error [E0525]: shallow spread of read-only record into 'let mut'

-- E0526: CollectionMutationDuringIterationError (mutating collection while iterating over it)
let mut nums = [1, 2, 3]
for item in nums {
    -- nums !> Array::push(item)       -- Error [E0526]: cannot mutate 'nums' in place while iterating in 'for' loop
}

-- E0527: ClosureCaptureLaunderingError / UnusedMutBindingError
let mut never_written = 42             -- Error [E0527]: variable 'never_written' declared 'let mut' but never modified
fn pass_to_mut(mut u: UserDoc) &mut { u.score += 1 }
-- pass_to_mut(mut doc)                -- Error [E0527]: cannot pass read-only handle 'doc' as 'mut' argument

-- E0528: ReturnMutabilityLaunderingError (returning read-only parameter into caller let mut)
fn inspect_user(u: UserDoc) -> UserDoc { u }
let user_in = UserDoc.{ title: "Alice", score: 10 }
let inspected = inspect_user(user_in)
-- let mut stolen = inspected          -- Error [E0528]: returned value originates from read-only parameter

-- E0529: ExcessiveCapabilityAnnotationError (over-annotating beyond minimal required capabilities)
-- fn pure_add(a: int, b: int) -> int &mut { a + b } -- Error [E0529]: function does not mutate parameters or state

-- E0530: IllegalCapabilityCloneImmutError (passing active capabilities or closures to clone_immut)
let mut counter_handle = create_counter(0)
-- let bad_immut = clone_immut(counter_handle) -- Error [E0530]: cannot freeze callable carrying mutable capabilities
```

### 8.8 Callable Signature Abstraction

Concrete captured variable names abstract behind `&closure`. Retained mutable sharing `&{^mut var}` cannot be erased: it MUST abstract to both `&closure` and anonymous `&^mut`. Casting stateful callables to unannotated pure functions is strictly rejected.

```ril
let mut SESSION_DATA = 0
let concrete_worker: fn(int) -> int &{mut SESSION_DATA} = \delta -> {
    SESSION_DATA += delta
    SESSION_DATA
}

-- 1. Valid Abstraction: Hiding variable name behind &closure
type Worker = fn(int) -> int &closure
let abstract_worker: Worker = concrete_worker -- OK: concrete &{mut SESSION_DATA} satisfies &closure

-- 2. Retained Sharing Abstraction: MUST retain &^mut
let mut HUB = Hub.{ entries: [] }
let concrete_stashing: fn(Entry) -> () &{^mut HUB} = \mut e -> {
    HUB.entries !> Array::push(e)
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

When an effect operation requires in-place mutation (e.g., writing into a caller-supplied buffer), it explicitly declares `&mut` on its operation signature. Callers invoking the operation and handlers servicing it must track, forward, or discharge this capability under standard capability tracking rules (§8). Concurrency boundaries (`nursery.spawn`, `par_map`) enforce Data-Race Freedom (DRF-SC) directly through capability checking: any value or closure crossing a concurrency boundary must not carry live mutable capabilities (`&mut`, `&^mut`, `&{mut var}`), rejected statically under `E0601: CrossThreadDataRaceHazardError`. No separate nominal `Shareable` trait is required.

```ril
-- 1. Pure Effect Operations & Ambient Context:
effect Console = {
    print: fn(str) -> (),
    read_line: fn() -> str,
}

effect Context<T> = {
    ask: fn() -> T,                    -- OK: Ambient context value
}

-- 2. Effect Operations Declaring Mutation Capabilities:
effect BufferIO = {
    read_into: fn(mut buf: []u8) -> int &mut, -- OK: Operation declares in-place buffer mutation
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

-- 3. Concurrent Task Boundary: DRF-SC Capability Enforcement (No Ad-Hoc Shareable Trait):
fn concurrent_boundary_check() {
    let immut_data = "immutable configuration"
    let mut local_buf = [0u8, 0u8, 0u8]

    nursery(\mut scope -> {
        -- OK: Immutable value has zero mutable capabilities, safely crosses task boundary:
        scope.spawn(\-> {
            immut_data
        })

        -- Error [E0601]: CrossThreadDataRaceHazardError: live mutable capability cannot cross task boundary
        -- scope.spawn(\-> {
        --     local_buf[0] = 1u8
        -- })
        Ok(())
    })
}
```

### 9.2 Effect Handlers (`with`)

`with` intercepts operations within its lexical scope, discharging the effect from the enclosing function's signature. When placed within a block, `with HandlerSpec` establishes the active deep handler for all subsequent expressions and statements in the remainder of that enclosing block. Handlers in Ril are **deep handlers**: invoking `resume(v)` does not discard the handler; it remains active for all subsequent effect invocations until the block terminates.

Closures constructed in a scope with an active `with` handler **automatically capture the handler** into their heap environment (`&closure`), safely discharging the effect from the closure's public signature. Closures carrying unhandled effects that escape to heap records without an in-scope handler are statically rejected (`E0614`).

```ebnf
WithExpr    ::= "with" HandlerSpec
HandlerSpec ::= "{" HandlerArm { "," HandlerArm } [ "," ] "}" | HandlerArm
HandlerArm  ::= QualifiedName "(" [ PatternList ] ")" "->" Expression
```

```ril
-- 1. Multi-Arm Statement Handler (like match block):
fn run_console() -> () {
    let mut log_entries: []str = []

    with {
        Console::print(msg) -> {
            log_entries !> Array::push(msg)
            resume(())                 -- Resumes computation; handler remains active
        },
        Console::read_line() -> resume("Alice"),
    }

    hello()                            -- All 3 Console operations intercepted deeply
    -- @Console is fully discharged; run_console is purely functional externally
}

-- 2. Single-Arm Statement Handler:
fn run_config() -> str {
    with Context::ask() -> resume("Production")
    Context::ask()                     -- Intercepted by single-arm handler
}

-- 3. Automatic Handler Capture in Escaping Closures:
type Button = { label: str, on_click: fn() -> () }

fn make_button() -> Button {
    with Console::print(msg) -> resume(())

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
        let first = resume(1)
        -- let second = resume(2)       -- Error [E0610]: affine resumption 'resume' invoked more than once
        first
    }
    Op::query()
}

-- 2. Escaping Resumption Violation: resume escaping the handler arm
fn bad_escaping_resume() -> fn() -> int {
    with Op::query() -> {
        let esc = \-> resume(42)        -- Error [E0611]: affine resumption 'resume' cannot escape handler arm
        esc
    }
    Op::query()
}

-- 3. Delimited Early Abort with Proven LIFO Cleanup & Commit-on-Write Memory:
effect Auth = {
    authenticate: fn() -> bool,
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
        with Auth::authenticate() -> "Aborted"  -- Early abort without resume()
        guarded_workflow(mut audit)
    }
    assert(res == "Aborted")
    -- Invariant: LIFO cleanups executed (session 1st, file 2nd); prior mutation "STEP_1" remains committed:
    assert(audit.entries == ["STEP_1", "CLEANUP_SESSION", "CLEANUP_FILE"]) -- OK
}
```

### 9.4 Built-in Effects (`@Async`, `@Fiber`, `@Concurrent`, `@Div`)

Ril provides four foundational built-in algebraic effects tracking execution capabilities:

1. **`@Fiber` (Cooperative Fiber Control)**: Low-level cooperative scheduling primitives (`yield`, `park`, `unpark`).
2. **`@Concurrent` (Structured Concurrency)**: High-level concurrent spawning, joining, racing, and timeout mechanics.
3. **`@Async` (Suspendable I/O)**: An effect alias `{Fiber, Concurrent}` tracking uncolored asynchronous computations.
4. **`@Div` (Divergence Tracking)**: Tracks potential non-termination in unbounded loops and general recursive functions. Total functions (`halt fn`) strictly prohibit `@Div`.

```ril
-- 1. Uncolored Asynchronous I/O (@Async):
fn fetch_user_data(url: str) -> str @Async {
    let response = Http::get(url)       -- Evaluates asynchronously with standard call syntax
    response.body                       -- Uncolored return type: str (not Promise<str>)
}

-- 2. Cooperative Fiber Yielding (@Fiber):
fn cooperative_worker(mut count: int) -> () @Fiber {
    while count > 0 {
        count -= 1
        Fiber::yield()                  -- Yields execution quantum to runtime scheduler
    }
}

-- 3. Divergence vs. Total Functions (@Div):
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

### 9.5 Structured Concurrency (`nursery`) & Isolated Panic Containment

All concurrent child tasks must be spawned within a structured `nursery`. A parent nursery cannot exit until all child tasks finish. Panics in child tasks are isolated at the nursery boundary and resolve to `Result<T, TaskFault>` (`TaskFault::Panicked`).

```ril
use ril/concurrent::{nursery, Scope, Task, TaskFault}

-- 1. Structured Concurrency and Task Panic Containment:
fn run_isolated_workers() -> Result<(str, int), TaskFault> {
    nursery(\mut scope -> {
        let task_ok = scope.spawn(\-> {
            "computation result"
        })

        let task_crash = scope.spawn(\-> {
            let divisor = 0
            100 / divisor              -- Child task panics: division by zero
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
        }

        Ok((ok_val, err_val))
    })
}

-- 2. Concurrency Safety: Rejecting live mutable view across task boundary
fn bad_concurrent_data_race() {
    let mut shared_data = [1, 2, 3]
    nursery(\mut scope -> {
        -- scope.spawn(\-> {            -- Error [E0601]: cannot capture mutable handle 'shared_data' across concurrent task boundary
        --     shared_data !> Array::push(4)
        -- })
        Ok(())
    })
}
```

### 9.6 Data Parallelism (`par_map`, `par_fold`) & Deterministic Reductions

`ril/parallel` evaluates data-parallel combinators across slice partitions. `par_fold` requires chunk-local accumulators with local `&mut`, avoiding cross-core cache invalidation. Reductions merge intermediate results via a canonical binary tree ($G_{\text{canonical}} = 64$) guaranteeing bit-for-bit floating-point determinism.

```ril
use ril/parallel::{par_map, par_fold}

let numbers: []f64 = [1.1, 2.2, 3.3, 4.4, 5.5, 6.6, 7.7, 8.8]

-- 1. Pure Data-Parallel Mapping:
let scaled = numbers |> par_map(\x -> x * 2.0)

-- 2. Floating-Point Deterministic Fold via Canonical Binary Reduction Tree (G_canonical = 64):
let total_sum = par_fold(
    numbers,
    init_acc: \-> 0.0f64,
    fold_local: \mut acc, x -> { acc += x }, -- OK: thread-local &mut accumulator
    merge_acc: \a, b -> a + b
)

-- 3. Capability Confinement: Rejecting external mutable captures in parallel combinator
let mut external_counter = 0
-- let bad = numbers |> par_map(\x -> {
--     external_counter += 1            -- Error [E0605]: cannot capture external mutable handle 'external_counter' in parallel combinator
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

2. **Expression Contexts**: In static type closures and expression positions, ALL types without exception MUST be enclosed in `type<...>`:

```ril
let t_int = type<int>                  -- OK: all types enclosed in type<...>
let t_inferred = type<typeof (1 + 2)>  -- OK: 'typeof' enclosed in type<...> in expression position
-- let bad_t = int                     -- Error [E0301]: bare type in expression context
-- let bad_inferred = typeof (1 + 2)   -- Error [E0301]: bare 'typeof' in expression context
```

3. **Static Closures & Invocation**: Unannotated static closure parameters default to sort `Type` (`\T -> ...`). Static closure application uses generic angle brackets `<...>`:

```ril
type Nullable = \T -> type<?T>
type PairOf = \T, U -> type<{ first: T, second: U }>

-- Applying static type closures via '<...>':
type IntNullable = Nullable<int>          -- Resolves to ?int
type StringIntPair = PairOf<str, int>     -- Resolves to { first: str, second: int }

let value: IntNullable = Some(42)         -- OK: used as concrete type annotation
let pair: StringIntPair = .{ first: "id", second: 101 }
```

### 10.2 Static Type Closures & Computation Model (`halt type`, `halt fn`)

1. **Return Invariant**: A static type closure is a compile-time function whose return expression MUST evaluate to a `type<T>`. Returning a non-type value raises `E0301`.
2. **Computation Semantics**: Closure bodies support standard local bindings (`let`), control flow (`if`, `match`), and invocations of `meta fn` callables.
3. **Totality Certification**: `halt type` certifies normal termination. Unmarked static closures operate under configurable compiler evaluation budgets (`E0811`).

```ril
-- 1. Meta helper function (compile-time pure calculation):
meta fn pad_align(size: int, align: int) -> int {
    (size + align - 1) & !(align - 1)
}

-- 2. Static type closure with control flow, meta computation, and type output:
halt type PaddedBuffer = \raw_size: int, T -> {
    let actual_size = pad_align(raw_size, 8)     -- OK: consumes meta fn and const value
    if actual_size > 1024 {
        type<{ heap_ptr: int, cap: int }>        -- Branch evaluates to type<T>
    } else {
        type<{ inline_data: []T, len: int }>     -- Branch evaluates to type<T>
    }
}

type FastBuf = PaddedBuffer<64, u8>              -- Resolves to { inline_data: []u8, len: int }

-- Static closure returning non-type is rejected:
-- type BadReturn = \T -> 42                     -- Error [E0301]: type closure must evaluate to type<T>, found int

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

1. **Family Isolation**: Static closures can invoke `meta fn` callables and static closures, but cannot invoke runtime `fn` callables (`E0810`).
2. **Runtime Isolation**: Runtime functions cannot invoke static type closures (`E0810`).
3. **Budget Exhaustion**: Exceeding compiler evaluation limits halts compilation with `E0811`.

```ril
fn runtime_helper() -> int { 42 }

-- Static closure cannot execute runtime function:
-- type BadStatic = \T -> {
--     let x = runtime_helper()        -- Error [E0810]: cannot invoke runtime function from compile-time static type closure
--     type<int>
-- }

-- Runtime function cannot invoke static type closure:
fn bad_runtime_fn() {
    -- let t = FastBuf<64, u8>         -- Error [E0810]: cannot invoke static type closure from runtime function
}

-- Compiler Evaluation Budget Exhaustion:
type RecursiveLoop = \T -> RecursiveLoop<T>
-- type Overflow = RecursiveLoop<int>  -- Error [E0811]: compile-time evaluation budget exceeded (max 100,000 steps)
```

### 10.4 Mapped Schemas (`keyof`, Field Indexing `T[K]`)

Static type closures inspect and transform record schemas using `keyof` and indexed field lookup `T[K]`:

```ril
type User = { id: int, name: str, active: bool }

-- 1. Schema Key Extraction (keyof):
type UserKeys = keyof User             -- Resolves to "id" | "name" | "active"

-- 2. Schema Field Indexing:
type IdType = User["id"]               -- Resolves to int

-- 3. Mapped Schema Construction:
type OptionalSchema = \T -> type<{
    [K in keyof T]: ?T[K]
}>

type UserPatch = OptionalSchema<User>
-- Resolves to: { id: ?int, name: ?str, active: ?bool }

let patch: UserPatch = .{ id: Some(1), name: None, active: Some(true) }
```

### 10.5 Static Parameter Sorts & Adaptation Rules (`\param: Sort`)

Static type closures accept four parameter sorts:

1. **Bare Types (`\T` or `\T: Type`)**: Accepts static type expressions. Unannotated parameters default to sort `Type`.
2. **Const Values (`\param: ValueType`)**: Accepts compile-time known constants (literals, `meta let`, statically foldable expressions). Passing runtime variables raises `E0810`.
3. **Bounded & Structural Types (`\T: { id: int, .. }`, `\K: keyof T`)**: Enforces structural row subtyping and key inclusion.
4. **Higher-Kinded Constructors (`\M: Type -> Type`)**: Enforces constructor kind arity (`E0306`).

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
type PickField = \T: { .. }, K: keyof T -> T[K]
type UserName = PickField<SchemaV1, "name"> -- Resolves to str
-- type BadField = PickField<SchemaV1, "missing"> -- Error [E0301]: "missing" not in keyof SchemaV1

-- Higher-kinded constructor adaptation:
type Wrapper = \M: Type -> Type, T -> M<T>
type OptInt = Wrapper<Option, int>      -- Resolves to Option<int>
-- type BadKind = Wrapper<int, int>     -- Error [E0306]: KindMismatchError, expected Type -> Type, found int
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

Every source file is an independent compilation unit. Top-level items are private to the file by default unless marked with `pub`.

```ril
-- In file: math/geometry.ril
let PI = 3.141592653589793              -- Private to module 'geometry'
pub let TAU = 6.283185307179586         -- Public: exported from module

pub fn circle_area(radius: f64) -> f64 {
    PI * radius * radius                -- OK: internal access to private 'PI'
}

-- In file: app/main.ril
use math/geometry::{TAU, circle_area}   -- OK: importing public symbols
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
let mut ACTIVE_WORKERS: int = 0        -- OK: initialized with constant expression

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
        Ok(())                          -- Exits cleanly with status code (0)
    }
}
```

### 11.6 Standard Prelude Built-ins

The following types and functions are implicitly available in every compilation unit:

| Item | Kind | Description |
| :--- | :--- | :--- |
| `Option<T>`, `?T` | Sum Type | Optional value: `Some(T)` or `None` |
| `Result<T, E>` | Sum Type | Fallible operation outcome: `Ok(T)` or `Err(E)` |
| `Map<K, V>`, `Set<T>` | Types | Built-in associative map and unique set |
| `inner(wrapper)` | Function | Extracts underlying value from nominal wrapper `type W(T)` |
| `clone(x)` | Function | Allocates deep independent mutable duplicate of heap reference |
| `clone_immut(x)` | Function | Freezes heap object into permanently immutable `Immut<T>` |
| `move(x)` | Function | Affinely invalidates local handle, transferring unaliased ownership |
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

-- 4. Affine Ownership Transfer via move():
let resource = "unaliased buffer"
let owned = move(resource)             -- 'resource' handle invalidated
-- print(resource)                     -- Error [E0606]: use of moved value 'resource'

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
    if user_id <= 0 { Err("invalid id") } else { Ok(()) }
}

fn process_request(id: int) -> Result<(), str> {
    -- Prohibited: discarding fallible Result without inspection
    -- save_profile(id)                 -- Error [E0720]: unused fallible Result must be handled

    -- Compliant Alternative 1: Postfix '?' error propagation
    save_profile(id)?

    -- Compliant Alternative 2: Explicit pattern matching
    match save_profile(id) {
        Ok(()) -> Logger::info("Profile saved"),
        Err(e) -> Logger::error("Save failed: " ++ e),
    }

    -- Compliant Alternative 3: Fallback error closure
    save_profile(id) ?? \err -> Logger::warn("Handled fallback: " ++ err)

    Ok(())
}
```

---

## 12. Diagnostic Error Codes Summary

| Code | Diagnostic Name | Normative Condition |
| :---: | :--- | :--- |
| **`E0201`** | `PrivateItemAccessError` | Accessing or importing unexported private module symbol |
| **`E0202`** | `TopLevelSideEffectError` | Top-level declaration contains non-constant runtime side effects |
| **`E0203`** | `DuplicateDeclarationError` | Redeclaring an existing identifier in the same scope |
| **`E0301`** | `TypeMismatchError` | Expression type incompatible with expected type |
| **`E0302`** | `UnexpectedFieldError` | Closed record supplied with undeclared fields |
| **`E0305`** | `NominalTypeMismatchError` | Mismatched nominal type wrapper identities |
| **`E0306`** | `KindMismatchError` | Mismatched higher-kinded type constructor or sort constraint |
| **`E0401`** | `ValueTypeMutableBorrowError` | Attempt to declare or pass a value type as `mut` parameter |
| **`E0501`** | `ImmutableReassignmentError` | Reassigning an immutable `let` binding |
| **`E0510`** | `MissingCapabilityAnnotationError` | Calling mutating operation without declaring `&mut` or `&^mut` |
| **`E0520`** | `MutabilityLaunderingError` | Binding read-only handle to `let mut` or mutating through view |
| **`E0521`** | `DestructureMutabilityLaunderingError` | Destructuring read-only handle into `mut` pattern fields |
| **`E0522`** | `ContainerMutabilityLaunderingError` | Injecting read-only reference into mutable collection |
| **`E0523`** | `MutMutAliasingConflictError` | Overlapping mutable arguments passed to `mut` parameters |
| **`E0524`** | `ReadMutAliasingHazardError` | Mutable argument aliases simultaneous read-only argument |
| **`E0525`** | `SpreadLaunderingError` | Shallow-spreading read-only record into `let mut` root |
| **`E0526`** | `CollectionMutationDuringIterationError` | Mutating collection in place while iterating in `for` loop |
| **`E0527`** | `UnusedMutBindingError` | `let mut` binding or `mut` parameter never modified |
| **`E0528`** | `ReturnMutabilityLaunderingError` | Returning read-only parameter into caller `let mut` handle |
| **`E0529`** | `ExcessiveCapabilityAnnotationError` | Over-annotating signature beyond minimal required capabilities |
| **`E0530`** | `IllegalCapabilityCloneImmutError` | Passing active capabilities or closures to `clone_immut` |
| **`E0601`** | `CrossThreadDataRaceHazardError` | Passing live mutable view across concurrent task boundary |
| **`E0605`** | `InvalidParallelCapabilityError` | Capturing external mutable capabilities in parallel combinator |
| **`E0606`** | `UseAfterMoveError` | Attempting to access an affinely moved handle |
| **`E0607`** | `DraftProxyEscapeError` | Attempting to return draft proxy out of `produce` recipe |
| **`E0610`** | `DuplicateResumeInvocationError` | Invoking affine one-shot resumption `resume` more than once |
| **`E0611`** | `EscapingResumeError` | Escaping resumption handle beyond handler arm lexical scope |
| **`E0614`** | `EscapingEffectClosureError` | Closure with unhandled effect escaping to heap record without in-scope handler |
| **`E0701`** | `ChainedAssignmentProhibitedError` | Chaining assignments (`a = b = c`) |
| **`E0702`** | `InvalidWhereItemError` | Declaring variable binding or non-hoistable item in `where` clause |
| **`E0710`** | `IllegalControlTransferInFallbackError` | Embedding `return`/`break` in fallback operator `??` |
| **`E0711`** | `InvalidResultFallbackError` | Supplying raw value fallback for `Result` without error closure |
| **`E0720`** | `UnusedFallibleResultError` | Discarding fallible `Result` without inspection |
| **`E0810`** | `CallFamilyViolationError` | Crossing disjoint runtime `fn` and compile-time `meta`/`type` call families |
| **`E0811`** | `CompileTimeBudgetExceededError` | Exhausting compiler evaluation step budget in meta/type closures |
| **`E0820`** | `TotalityViolationError` | Totality certification failed in `halt fn` (unbounded recursion/loop) |
| **`E0830`** | `MetaAssertionFailedError` | Compile-time `assert` condition evaluated to `false` in `meta` context |
