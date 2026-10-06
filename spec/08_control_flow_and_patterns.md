# 08. Control Flow and Pattern Matching

This chapter specifies control flow expressions, loop constructs, pattern matching mechanics, record iteration, exhaustiveness algorithms, and diverging destructuring in Ril.

---

## 1. Block Expressions and Sequencing

A block expression groups declarations (items) and expressions, executing them sequentially and evaluating to a final result:

```ebnf
BlockItem  ::= Item | Expression
Block      ::= "{" { Separator } [ BlockItem { Separators BlockItem } [ Separators ] ] [ WhereBlock ] "}"
WhereBlock ::= "where" { Separator } FunctionDecl { Separators FunctionDecl } [ Separators ]
```

### 1.1 Block Evaluation Rules

1. **Empty Block**: An empty block `{}` statically evaluates to the unit value `()` of type `()`.
2. **Sequential Discarding**: Non-tail expressions in a sequence evaluate for side effects. Their values are discarded:
   - Discarding an expression evaluating to `Result<T, E>` without handling is a compile-time static error (`UnusedResultError`).
   - Discarding an affine scope-locked resource handle (`LockedToScope`) without binding is a compile-time static error (`MustBindAffineObligationError`).
3. **Tail Value Resolution**:
   - The value of a block is the value of its final expression if and only if it is NOT followed by a semicolon `;`. Its static type is the type of that tail expression.
   - If the final expression is followed by a semicolon (`;`), its value is discarded, and the block evaluates to the unit value `()`.
   - If the block terminates in an `Item` (such as a `let` binding or a local type declaration), the block evaluates to `()`.
   - Trailing newlines following the final expression preserve its value and do NOT discard it.
4. **Trailing `where` Hoisting**:
   A block MAY append a trailing `where` section declaring subordinate functions. Declarations under `where` are hoisted into the enclosing block scope, allowing primary logic to precede helper definitions without affecting type inference or scope resolution. The tail expression of the block is determined immediately preceding the `where` keyword.

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
5. **`else` Line Continuation Across Newlines**: Across newlines, when an `else` keyword immediately follows the closing brace `}` of an `if` expression or `let` declaration, it continues the preceding construct rather than separating items or expressions (see [§03 (Formal Grammar and Syntax)](03_formal_grammar_and_syntax.md)).

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
WhileExpr ::= "while" ( "let" Pattern "=" Expression [ "if" Expression ] | Expression ) Block
```

1. Evaluates its condition before each iteration, executing the block while the condition evaluates to `true` or pattern matching succeeds.
2. **Evaluates to Unit**: When the condition terminates or becomes false, the `while` expression evaluates to the unit value `()`.

### 3.3 Iteration Loops (`for`)

```ebnf
ForBindings ::= "as" Pattern [ "," Pattern ]
ForExpr     ::= "for" Expression ForBindings Block
```

1. **Single Evaluation of Source**: The iterated collection expression evaluates exactly once before iteration begins.
2. **Collection Kinds**:
   - **Arrays (`[]T`) and Slices**: Yields elements of type `T`. An optional second binding captures the 0-based iteration index as `int`.
   - **Byte Buffers (`bytes`)**: Yields unsigned byte values of type `u8`.
   - **Maps (`Map<K, V>`)**: Yields key and value: `for map as key, value` binds `key: K` and `value: V`. Alternatively, a single 2-tuple pattern `for map as (k, v)` destructures the entry.
   - **Integer Ranges (`start..end`)**: Yields ascending integers of the range's integer type.
3. **Pattern Destructuring in Loop Headers**:
   The element binding accepts full pattern destructuring, including tuple patterns `(a, b)` and record patterns `.{ x, y }`.
4. **Evaluates to Unit**: Upon exhaustion of the iterated collection, the `for` expression evaluates to the unit value `()`.

### 3.4 Record Iteration (`for record as key, value`)

For a non-dependent record `record: T`:

```ril
type Entry = { name: str, count: int }
let row = Entry.{ name: "Lin", count: 2 }
for row as key, value {
    -- key: keyof Entry (correlated), value: Entry[key]
}
```

1. **Shallow Copy of Keys**: Iteration reads a shallow copy of keys before iteration begins and visits labels in **lexicographic Unicode scalar order**.
2. **Typing Invariants**: In each iteration, `key: keyof T` is stable and `value: T[key]`. The loop body MUST typecheck for every admitted label.
3. **Single Binder**: With one binder `for record as entry`, the item is a compiler-checked correlated entry package: its key determines the projected value type. This special record eliminator is not a general runtime dependent-record feature.
4. **Prohibition of Dependent Records**: Existential/binder-dependent packages and records with opaque type members are NOT runtime record iteration sources and MUST be rejected at compile time.

---

## 4. Pattern Syntax and Destructuring

```ebnf
Pattern            ::= SinglePattern { "|" SinglePattern } [ "as" [ "mut" ] Identifier ]
PatternList        ::= Pattern { "," Pattern } [ "," ]
SinglePattern      ::= [ "mut" ] ( LiteralPattern | RangePattern | NamePattern | RecordPattern | TuplePattern | ArrayPattern | WildcardPattern )
LiteralPattern     ::= LiteralType
NamePattern        ::= QualifiedName [ "(" [ PatternList ] ")" ]
WildcardPattern    ::= "_"
RangePattern       ::= LiteralPattern ( ".." | "..=" ) LiteralPattern
ArrayRestPattern   ::= "..." [ "mut" ] [ Identifier ]
ArrayPattern       ::= "[" [ ( Pattern | ArrayRestPattern ) { "," ( Pattern | ArrayRestPattern ) } [ "," ] ] "]"
RecordPatternField ::= [ "mut" ] Identifier [ ":" Pattern ]
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

### 4.4 Alias Patterns (`P as name`)

An alias pattern binds the entire matched value of the pattern disjunction or sub-pattern to the identifier `name`. The static type of `name` is the unified type of the matched pattern.

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
5. **Unreachable Arm Static Rejection (`UnreachablePatternError`)**:
   A match arm that is provably unreachable due to being shadowed by preceding exhaustive or identical patterns MUST be rejected at compile time as a static error.

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

Diverging destructuring is a form of variable binding declaration (`LetDecl`, see [06. Declarations and Items](06_declarations_and_items.md)) applicable when a pattern is refutable:

```ril
fn get_user(id: int) -> Result<str, str> {
    let Some(name) = find_by_id(id) else {
        return Err("not found") -- MUST diverge
    }
    Ok(name)
}
```

1. **Mandatory Divergence**: The `else` block of a `let ... else` declaration **MUST diverge**: it MUST have static type `never` and exit the current control scope via `return`, `break`, `continue`, or `panic()`. Falling through the `else` block is a compile-time static error.
2. **Refutability Requirement (`IrrefutablePatternElseError`)**: The pattern in a `let ... else` construct MUST be refutable. Applying `let ... else` to a statically irrefutable pattern is a compile-time static error.
3. **Scope and Visibility Invariant**:
   - Variables bound in `Pattern` enter scope strictly for subsequent items and expressions in the enclosing block upon successful matching.
   - Variables bound in `Pattern` are strictly **NOT in scope** within the `else` block.
4. **Desugaring Equivalence**:
   `let p = expr else { block }` is operationally equivalent to:
   ```ril
   match expr {
       p -> (),
       _ -> block,
   }
   ```
   with the successful bindings introduced into the succeeding frame.
5. **Item Status**: As an `Item`, `let ... else` produces no runtime value. If positioned as the terminal element of a block, the block evaluates to `()`.

## 7. Static Closure Control Flow

Static type closures reuse ordinary block, let, if, match, return, closure and finite traversal rules. Ordinary type closures may use general recursion/loops under compile-time purity, stage checks and resource budgets. Halt type closures use Chapter 12's normal-return and termination rules; stable finite for traversal is permitted only with certified primitives/iterators. They cannot invoke runtime functions.

TypeMatch arms return ordinary static expressions with a consistent sort. Unknown type inputs block reduction rather than selecting a fallback. Type tuple rest patterns bind a tuple Type, distinct from runtime array/tuple destructuring.
