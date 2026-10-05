# 03. Formal Grammar and Syntax

This chapter defines the syntactic conventions, formal operator precedence hierarchy, item and expression sequencing rules, and structural disambiguation boundaries of Ril.

For the complete, machine-readable formal grammar of all declarations, types, and expressions, see [Appendix: Consolidated Formal EBNF Grammar](appendix_ebnf_grammar.md).

---

## 1. Grammar Notation (EBNF)

The formal grammar of Ril is specified using Extended Backus-Naur Form (EBNF) with the following standard conventions:

- `Production ::= Expression`: Defines a non-terminal rule.
- `"literal"` or `'literal'`: Exact terminal string or token.
- `A B`: Concatenation (sequence of `A` followed by `B`).
- `A | B`: Alternation (choice of either `A` or `B`).
- `[ A ]`: Optional element (zero or one occurrence of `A`).
- `{ A }`: Repetition (zero or more occurrences of `A`).
- `( A )`: Grouping.
- `(* comment *)`: Explanatory grammar comment.

---

## 2. Item and Expression Sequencing and Layout Rules

Ril uses a combination of explicit semicolons (`;`) and semantic newlines to sequence declarations (items) and expressions within blocks and module scopes.

```ebnf
Separator  ::= ";" | Newline
Separators ::= Separator { Separator }
```

### 2.1 Semicolon and Newline Rules

1. **Item and Expression Separation**: Expressions and item declarations in a block or module scope are separated by semicolons or newlines.
2. **Block Tail Expression**:
   - The value of a block expression `{ ... }` is the value of its final expression if not followed by a semicolon.
   - If the final expression is followed by a semicolon (`;`), its evaluated value is discarded, and the block evaluates to the unit value `()`.
   - Trailing newlines following a block's final expression preserve its value and do NOT discard it to `()`.
   - An empty block `{}` or a block terminating in an item declaration evaluates to `()`.
3. **Line Continuation**:
   A newline character is treated as whitespace (continuation) rather than a separator under any of the following conditions:
   - When the newline immediately follows a binary operator, assignment operator (`=`), arrow (`->`), or comma (`,`).
   - When the newline immediately precedes a leading pipeline operator (`|>`), mutating pipeline (`!>`), or fallback operator (`??`).
   - Within balanced enclosing delimiters: parentheses `(...)`, brackets `[...]`, or generic angle brackets `<...>`.

### 2.2 Dedicated Line-Breaking Rules

1. **Multiline Function Signatures**:
   In function declarations, the return type annotation `-> ReturnType` and each effect or capability annotation (`@Effect`, `&mut`, `&^mut`, `&capture`) MAY appear on dedicated separate lines following the parameter list.
2. **Postfix Error Operator (`?`) Line Rule**:
   In postfix error mapping `expr ? mapper`, the `mapper` expression MUST begin on the same physical line as the `?` token without an intervening newline. A newline immediately following `?` terminates the operator as a standalone postfix unwrap.
3. **Control Transfer Terminations**:
   A newline immediately following `return` or `break` concludes a bare control transfer expression yielding `()`. Any optional return or break payload expression MUST begin on the same physical line.
4. **`else` Line Continuation Rule**:
   When a newline immediately follows the closing brace `}` of an `if` expression or `let` declaration, and the first non-whitespace token on the subsequent physical line is `else`, the newline is treated as a continuation rather than an expression separator, binding the `else` branch directly to that preceding construct.

---

## 3. Operator Precedence and Associativity Table

The table below establishes the strict precedence hierarchy of all operators and syntactic constructs, ordered from highest precedence (Level 1) to lowest precedence (Level 17).

| Level | Operators / Syntactic Forms | Associativity | Description |
| :---: | :--- | :---: | :--- |
| **1** | `.` `?.` `?[]` `[]` `()` `::` postfix `?` | **Left** | Member access, safe navigation, indexing, invocation, namespace path, postfix error propagation/mapping |
| **2** | `-` `!` `~` `typeof` | **Unary Prefix** | Arithmetic negation, logical NOT, bitwise NOT, static type introspection |
| **3** | `*` `/` `%` `*%` | **Left** | Multiplication, division, remainder, wrapping multiplication |
| **4** | `+` `-` `+%` `-%` | **Left** | Addition, subtraction, wrapping addition & subtraction |
| **5** | `<<` `>>` | **Left** | Bitwise shift left, bitwise shift right |
| **6** | `&` | **Left** | Bitwise AND |
| **7** | `^` | **Left** | Bitwise XOR |
| **8** | `\|` | **Left** | Bitwise OR |
| **9** | `..` `..=` | **Non-associative** | Half-open and inclusive range construction (`a..b..c` is a static error) |
| **10** | `<` `>` `<=` `>=` `is` `in` | **Non-associative** | Relational comparisons, variant test, erased key membership (`a < b < c` is a static error) |
| **11** | `==` `!=` | **Left** | Equality and inequality |
| **12** | `&&` | **Left** | Logical AND (short-circuiting) |
| **13** | `\|\|` | **Left** | Logical OR (short-circuiting) |
| **14** | `\|>` | **Left** | Linear pipeline data-flow operator |
| **15** | `!>` | **Non-associative** | Single-use mutating pipeline operator (**strictly single-use; chaining is a static error**) |
| **16** | `??` | **Right** | Lazy fallback and unwrapping operator |
| **17** | `=` `+=` `-=` `*=` `/=` `%=` `+%=` `-%=` `*%=` `&=` `^=` `\|=` `<<=` `>>=` | **Non-associative** | Value and compound assignment (**evaluates to `()`**) |

*Note on relational `in`*: Key membership `in` (as in `k in keyof T`) has relational precedence (Level 10) and is available exclusively within erased compile-time computations.

*Note on Primary and Control Expressions*: Literals, identifiers, blocks, parenthesized expressions, control flow expressions (`if`, `match`, `loop`, `while`, `for`), control transfer expressions (`return`, `break`, `continue`), effect handling expressions (`with`), and delimited resumptions (`resume`) are Primary Expressions (`PrimaryExpr`). They participate in binary and postfix operations through explicit grouping or their syntactic delimiter boundaries.

---

## 4. Syntactic Disambiguation and Boundary Invariants

### 4.1 Mutating Pipeline Operator (`!>`) Single-Use Rule

The mutating pipeline operator `!>` forwards a mutable lvalue target into a mutating function call as a `mut` parameter:

```ril
target !> mutating_fn(arg)
```

1. **Non-Associativity**: `!>` is strictly non-associative. Chaining `!>` with another `!>` (e.g., `a !> f() !> g()`) is a compile-time static error.
2. **Prohibition of Pipeline Mixing**: `!>` MUST NOT be chained with linear pipelines `|>` (e.g., `a !> f() |> g()` and `a |> f() !> g()` are static errors).
3. **LValue Invariant**: The left-hand side of `!>` MUST resolve to a valid mutable storage location (`AssignTarget`). Passing an rvalue or immutable binding is a static error.

### 4.2 Inline Closure Boundaries

When a closure expression `\x -> body` appears as an unparenthesized sub-expression, its body extends rightward up to the nearest enclosing delimiter boundary. However:
- At the outer delimiter depth of an inline closure, pipeline operators (`|>`, `!>`) and the fallback operator (`??`) MUST NOT be parsed as part of the closure body; they terminate the closure and attach to the closure's result or surrounding pipeline.
- To embed a pipeline or fallback within a closure body, the body MUST be enclosed in explicit parentheses `(\x -> (x |> f))` or a block `\x -> { x |> f }`.

### 4.3 Block Trailing `where` Clauses

A block expression `{ ... }` MAY append a trailing `where` clause following its final expression:

```ebnf
BlockItem  ::= Item | Expression
Block      ::= "{" { Separator } [ BlockItem { Separators BlockItem } [ Separators ] ] [ WhereBlock ] "}"
WhereBlock ::= "where" { Separator } FunctionDecl { Separators FunctionDecl } [ Separators ]
```

1. Functions declared under `where` are hoisted into the enclosing block scope, permitting the primary logic and return value to appear physically before subordinate local functions.
2. The block's evaluated result remains the value of the final expression immediately preceding the `where` keyword.

### 4.4 Disambiguation of `.{ ... }`

The literal form `.{ ... }` is context-dependent:
1. When checked against an expected record schema type, it parses as a **record literal** with bare field identifiers (`.{ field: val }`).
2. When checked without an expected record schema, or when containing bracketed keys (`.{ [expr]: val }`) or string literal keys (`.{ "key": val }`), it parses as a **Map literal** (`Map<K, V>`).
3. An empty `.{}` in an untyped context evaluates to an empty `Map`.

### 4.5 Additional Syntactic Disambiguation Invariants

1. **Standalone Postfix `?` Unwrap Access**:
   A same-line mapper after `?` absorbs its immediate field accesses, indices, and calls (`res ? Mapper.field`). To call or access the unwrapped *success* value instead, the standalone unwrap MUST be explicitly parenthesized: `(res?).field` or `(res?)[0]`.
2. **Lexical Disambiguation of `>` in Generics**:
   In type expressions, each `>` token closes exactly one generic argument list. Consecutive closing brackets (`>>` or `>>>`) MUST NOT be lexically scanned as bitwise shift operators; they are parsed as multiple individual `>` closers.
3. **Tuple Index Termination**:
   A positional tuple index ends immediately before the next `.` delimiter. In successive positional projections such as `pair.0.1`, `pair.0` is parsed as a complete projection before resolving `.1`.
4. **Pattern Names vs. Variant Discriminants**:
   In pattern matching, a bare unqualified name denotes a sum type variant constructor if and only if it resolves to a visible variant tag of the matched type; otherwise, it binds a fresh local variable. Qualified names (`Type::Variant`) always denote variant constructors.
5. **Callable Return Type Parenthesization**:
   A callable whose return type is another callable MUST enclose the inner callable in parentheses if it carries effects or state capabilities:
   ```ril
   fn() -> (fn() -> int @Log) &capture
   ```
   Effects and capability annotations outside the closing parenthesis belong to the enclosing outer callable signature.

### 4.6 Disambiguation of Contextual Keyword `scoped`

In `let` declarations, `scoped` is recognized as the resource scope modifier if and only if it is immediately followed by a pattern binder (such as `mut`, an identifier, `_`, `(`, `[`, or `.{`). When immediately followed by `=` or `:`, `scoped` is parsed as an ordinary variable identifier (e.g., `let scoped = 1`).
