# 08. Control Flow and Pattern Matching

This chapter specifies control flow expressions, loop constructs, pattern matching mechanics, record iteration, exhaustiveness algorithms, and diverging destructuring in Ril.

---

## 1. Block Expressions and Sequencing

A block expression groups statements and evaluates to a final result:

```ebnf
Block      ::= "{" { Separator } [ Statement { Separators Statement } [ Separators ] ] [ WhereBlock ] "}"
WhereBlock ::= "where" { Separator } FunctionDecl { Separators FunctionDecl } [ Separators ]
```

1. **Sequencing**: Expressions within a block execute sequentially from first to last.
2. **Block Value**:
   - The value of a block is the value of its final expression, unless terminated with a semicolon `;`, which discards the value to `()`.
   - Trailing newlines following the final expression preserve its value.
3. **Trailing `where` Hoisting**:
   A block MAY append a trailing `where` section declaring subordinate functions. Declarations under `where` are hoisted into the enclosing block scope, allowing primary logic to precede helper definitions without affecting type inference or scope resolution.

---

## 2. Conditionals (`if` and `if let`)

```ebnf
IfExpr ::= "if" ( "let" Pattern "=" Expression [ "if" Expression ] | Expression ) Block [ "else" ( IfExpr | Block ) ]
```

1. **Boolean Condition**: In `if cond { ... } else { ... }`, `cond` MUST have type `bool`.
2. **Conditional Pattern Binding (`if let`)**:
   `if let pat = expr` attempts to match `expr` against `pat`. If the match succeeds, bound identifiers enter the scope of the `if` block.
3. **Pattern Guards**: `if let pat = expr if guard` evaluates the boolean `guard` expression only if the pattern match succeeds. If the guard evaluates to `false`, control falls through to the `else` branch.
4. **Branch Type Agreement**: Both the `if` branch and `else` branch MUST produce expressions belonging to a common unified type. If an `else` branch is omitted, the `if` expression MUST evaluate to `()`.
5. **Dangling `else` Association Across Newlines**: Across newlines, `else` attaches to the innermost preceding conditional or loop construct at the same delimiter depth that lacks an `else` branch.

---

## 3. Loop Constructs (`loop`, `while`, `for`)

### 3.1 Infinite Loops (`loop`)

```ebnf
LoopExpr ::= "loop" Block
```

1. Evaluates its block indefinitely until terminated by `break` or `return`.
2. **Value-Bearing Break**: `break expr` terminates the loop and yields `expr` as the value of the `loop` expression.
3. If all break expressions yield values of type `T`, the `loop` expression has type `T`. If a `loop` contains no `break` expressions, its static type is `never`.

### 3.2 Conditional Loops (`while` and `while let`)

```ebnf
WhileExpr ::= "while" ( "let" Pattern "=" Expression [ "if" Expression ] | Expression ) Block [ "else" Expression ]
```

1. Evaluates its condition before each iteration, executing the block while the condition evaluates to `true` or pattern matching succeeds.
2. **Optional `else` Fallback**:
   - The `else` clause evaluates if and only if the loop condition terminates normally without executing a `break`.
   - The static type of all `break` values and the `else` expression MUST unify to a common type. If `else` is omitted, the loop evaluates to `()`.

### 3.3 Iteration Loops (`for`)

```ebnf
ForBindings ::= "as" Pattern [ "," Pattern ]
ForExpr     ::= "for" Expression ForBindings Block [ "else" Expression ]
```

1. **Single Evaluation of Source**: The iterated collection expression evaluates exactly once before iteration begins.
2. **Collection Kinds**:
   - **Arrays (`[]T`) and Slices**: Yields elements of type `T`. An optional second binding captures the 0-based iteration index as `int`.
   - **Byte Buffers (`bytes`)**: Yields unsigned byte values of type `u8`.
   - **Maps (`Map<K, V>`)**: Yields key and value: `for map as key, value` binds `key: K` and `value: V`. Alternatively, a single 2-tuple pattern `for map as (k, v)` destructures the entry.
   - **Integer Ranges (`start..end`)**: Yields ascending integers of the range's integer type.
3. **Pattern Destructuring in Loop Headers**:
   The element binding accepts full pattern destructuring, including tuple patterns `(a, b)` and record patterns `.{ x, y }`.
4. **Optional `else` Fallback on `for`**:
   The `else` clause evaluates if the loop exhausts all elements without executing a `break`. The static types of all `break` values and the `else` expression MUST unify to a common type.

### 3.4 Record Iteration (`for record as key, value`)

For a non-dependent record `record: T`:

```ril
type Row = { name: str, count: int }
let row = Row.{ name: "Lin", count: 2 }
for row as key, value {
    -- key: keyof Row (stable), value: Row[key]
}
```

1. **Shallow Snapshot**: Iteration reads one shallow snapshot before iteration begins and visits labels in **lexicographic Unicode scalar order**.
2. **Typing Invariants**: In each iteration, `key: keyof T` is stable and `value: T[key]`. The loop body MUST typecheck for every admitted label.
3. **Single Binder**: With one binder `for record as entry`, the item is a dependent entry record `{ key: keyof T, value: T[key] }`.
4. **Prohibition of Dependent Records**: Dependent records and erased fields are NOT runtime record iteration sources and MUST be rejected at compile time.

---

## 4. Pattern Syntax and Destructuring

```ebnf
Pattern            ::= SinglePattern { "|" SinglePattern }
SinglePattern      ::= [ "mut" ] ( LiteralPattern | RangePattern | NamePattern | RecordPattern | TuplePattern | ArrayPattern | WildcardPattern )
LiteralPattern     ::= LiteralType
NamePattern        ::= QualifiedName [ "(" [ PatternList ] ")" ]
WildcardPattern    ::= "_"
RangePattern       ::= LiteralPattern ( ".." | "..=" ) LiteralPattern
ArrayRestPattern   ::= "..." [ "mut" ] [ Identifier ]
ArrayPattern       ::= "[" [ ( Pattern | ArrayRestPattern ) { "," ( Pattern | ArrayRestPattern ) } [ "," ] ] "]"
RecordPatternField ::= Identifier [ ":" Pattern ]
RecordPattern      ::= [ TypeReference ] ".{" [ ( RecordPatternField | ".." ) { "," ( RecordPatternField | ".." ) } [ "," ] ] "}"
TuplePattern       ::= "(" Pattern "," [ Pattern { "," Pattern } [ "," ] ] ")" | "(" ")"
```

### 4.1 Record Pattern Punning

Within a record pattern `.{ ... }`, a bare identifier without an explicit sub-pattern (e.g., `.{ id, name }`) binds local variables with the identical names to those record fields.

### 4.2 Or-Patterns (`P1 | P2`)

Patterns MAY be joined with vertical bars to form disjunctive patterns.
- **Variable Binding Invariant**: If an Or-pattern binds variables, **every alternative branch in the disjunction MUST bind the identical set of variable names with matching static types**.

### 4.3 Pattern Name Resolution

- A bare unqualified identifier in a pattern resolves to a sum type variant constructor if it names a visible variant tag of the matched type; otherwise, it binds a fresh local variable.
- Qualified names (`Type::Variant`) always resolve to variant constructors. The wildcard `_` always matches without binding.

---

## 5. Match Expressions and Exhaustiveness

```ebnf
MatchArm  ::= Pattern [ "if" Expression ] "->" Expression
MatchExpr ::= "match" Expression "{" [ MatchArm { "," MatchArm } [ "," ] ] "}"
```

1. **Sequential Matching**: Arms are evaluated sequentially from top to bottom. The first arm whose pattern matches and whose optional `if` guard evaluates to `true` is selected.
2. **Mandatory Exhaustiveness**:
   - Every `match` expression MUST be statically exhaustive. A match lacking full coverage of the scrutinee's type MUST be rejected at compile time.
3. **Indexed Constructor Refinement**:
   When matching an indexed sum type (GADT), matching on a specific constructor refines type indices, allowing constructors with impossible index equations to be omitted from exhaustiveness requirements.
4. **Guards and Exhaustiveness**:
   An arm with an `if` guard is treated as potentially non-matching by the exhaustiveness checker and does NOT contribute to proving full type coverage.

---

## 6. Variant Discriminant Testing (`is`)

The binary operator `is` performs shallow discriminant testing on sum type variants without binding or extracting payloads:

```ril
let opt = Some(42)
opt is Some             -- evaluates to true
!(opt is None)          -- evaluates to true via logical NOT
```

1. **Static Typing**: `expr is Variant` requires `expr` to have a sum type that admits `Variant`.
2. **Payload Independence**: Discriminant testing checks only the tag; variant payloads are ignored and not evaluated.

---

## 7. Diverging Destructuring (`let ... else`)

```ebnf
LetElseStmt ::= "let" Pattern "=" Expression "else" Block
```

When a pattern is refutable (may fail to match), it MUST use `let ... else`:

```ril
fn get_user(id: int) -> Result<str, str> {
    let Some(name) = find_by_id(id) else {
        return Err("not found") -- MUST diverge
    }
    Ok(name)
}
```

1. **Mandatory Divergence**: The `else` block of a `let ... else` statement **MUST diverge**: it MUST exit the current control scope via `return`, `break`, `continue`, or `panic()`. Falling through the `else` block is a compile-time static error.
2. **Scope of Bindings**: Variables bound in `Pattern` are in scope for all statements following the `let ... else` construct in the enclosing block.
