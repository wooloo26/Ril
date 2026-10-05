# 07. Expressions and Operators

This chapter specifies the evaluation semantics, typing rules, desugaring equations, and operational panic conditions for all expressions and operators in Ril.

---

## 1. Expression-Oriented Evaluation

Ril is a 100% pure expression-oriented programming language. Every executable construct evaluates to a value (or diverges) and possesses a static type `τ`, a state capability set `σ`, and an algebraic effect set `ε`.

The language enforces a strict binary orthogonal architecture between declarations (**Items**) and executable terms (**Expressions**):
1. **Items**: Pure syntactic declarations (`let`, `fn`, `type`, `effect`, `module`, `use`, `test`) that extend the static typing environment `Γ`. Items produce no runtime values.
2. **Expressions**: All executable computational units. Blocks, conditionals, pattern matching, loops, pipeline stages, effect handlers (`with`), delimited resumptions (`resume`), and assignments are expressions.

There is NO concept of a "statement" in Ril.

---

## 2. Arithmetic and Numeric Operators

### 2.1 Checked Arithmetic (`+`, `-`, `*`, `/`, `%`, unary `-`)

1. **Homogeneous Typing**: Binary arithmetic operators require both operands to possess the identical numeric type and yield that exact type. Mixing different numeric types (e.g., `10 + 1.0` or `10i32 + 20i64`) is a compile-time static error.
2. **Deterministic Overflow Panics**: Fixed-width integer addition (`+`), subtraction (`-`), multiplication (`*`), and negation (`-`) MUST raise a runtime panic if the mathematical result exceeds the representable range of the operand type.
3. **Unsigned Negation**: Unary negation applied to an unsigned integer type (`u8`, `u16`, `u32`, `u64`) is a compile-time static error.
4. **Division and Remainder**:
   - Integer `/` truncates toward zero.
   - Integer `%` computes the remainder such that `(a / b) * b + (a % b) == a`. The sign of the remainder matches the sign of the dividend.
   - Integer division or remainder where the divisor is zero MUST trigger a runtime panic (`panic: integer division by zero`).
   - Signed minimum divided by `-1` (e.g., `i32(-2147483648) / -1`) overflows and MUST trigger a runtime panic. Its remainder `i32(-2147483648) % -1` evaluates to `0`.
5. **Arbitrary-Precision Integers (`bigint`)**: Arithmetic on `bigint` values never overflows a fixed bit-width and automatically expands to accommodate any finite integer result.

### 2.2 Explicit Wrapping Arithmetic (`+%`, `-%`, `*%`)

To support hashing, cryptography, and low-level algorithms, Ril provides explicit wrapping operators:

```ril
let x: u8 = 255u8 +% 1u8 -- evaluates to 0u8
let y: u8 = 0u8 -% 1u8   -- evaluates to 255u8
```

1. **Operand Types**: Defined on fixed-width integer types (`i8`..`i64`, `u8`..`u64`).
2. **Two's Complement Wrapping**: Operations compute mathematical results modulo $2^N$ under two's-complement representation.
3. **Panic Immunity**: Wrapping operators NEVER trigger overflow panics.

### 2.3 Bitwise Operators (`&`, `^`, `|`, `~`, `<<`, `>>`)

1. **Bitwise Logic**: `&` (AND), `^` (XOR), `|` (OR), and unary `~` (NOT) operate on bitwise patterns of fixed-width integers and `bigint`.
2. **Shift Operators (`<<`, `>>`)**:
   - The left operand is any integer type; the right operand (shift count) MUST have type `int`.
   - The shift count MUST be non-negative and strictly less than the bit width $N$ of the left operand ($0 \le \text{count} < N$).
   - A negative shift count or a count $\ge N$ MUST trigger a runtime panic without silent bitmasking.
   - `<<` is checked multiplication by $2^{\text{count}}$: for fixed-width integers, if any high bits are shifted out or the sign bit changes unexpectedly, it MUST trigger an overflow panic.
   - `>>` performs arithmetic right shift (sign extension) on signed integers and logical right shift (zero fill) on unsigned integers.

### 2.4 Floating-Point Semantics (IEEE 754)

1. **Standard Conformance**: Operations on `f32` and `f64` conform to IEEE 754 round-to-nearest, ties-to-even.
2. **Special Values**: Signed zeros (`+0.0`, `-0.0`), signed infinities (`+inf`, `-inf`), and NaN values propagate according to IEEE 754 without panicking. Division by zero yields signed infinity or NaN.
3. **Floating Remainder (`%`)**:
   - Floating-point `%` computes remainder with a quotient truncated toward zero: the exact remainder is rounded to the destination float type and carries the dividend's sign.
   - A finite dividend modulo infinity is unchanged. An infinite dividend or a zero divisor evaluates to `NaN`.
4. **Comparisons with NaN**:
   - `NaN == NaN` evaluates to `false`.
   - `NaN != NaN` evaluates to `true`.
   - All relational comparisons (`<`, `<=`, `>`, `>=`) involving NaN evaluate to `false`.

### 2.5 Explicit Primitive Conversions (`T(value)`)

Explicit conversion syntax `T(value)` converts a primitive or numeric expression to type `T`:

```ril
int(3.9)                            -- 3: truncates toward zero
f64(42)                             -- 42.0
i64(i32(42))                        -- 42 (i64)
bigint(u64(18446744073709551615))   -- 18446744073709551615 (bigint)
f32(16777217)                       -- 16777216.0 (f32): rounded to nearest, ties to even

fn narrow(value: int) -> u8 { u8(value) }
narrow(255)                         -- 255 (u8)
narrow(256)                         -- panic: integer conversion out of range
narrow(-1)                          -- panic: integer conversion out of range
int(1.0 / 0.0)                      -- panic: infinity cannot be converted to an integer
int(0.0 / 0.0)                      -- panic: NaN cannot be converted to an integer

str(true)                           -- "true"
bytes("abc")                        -- bytes: UTF-8 encoding
str(b"abc")                         -- str: UTF-8 decoding (lossy: replaces invalid sequences with U+FFFD)
```

1. **Integer-to-Integer Conversion**: Preserves the mathematical value. If the value falls outside the representable range of destination type `T`, evaluation MUST raise a runtime panic (`panic: integer conversion out of range`). Explicit conversion NEVER wraps.
2. **Float-to-Integer Conversion**: Truncates the floating-point value toward zero, then validates against the destination integer range. Converting `NaN`, positive infinity, negative infinity, or out-of-range values MUST raise a runtime panic. `bigint` accepts every finite truncated floating-point value.
3. **Float Conversions**: Converting a numeric value to `f32` or `f64` rounds to the nearest representable float value, with ties rounding to even. Overflow yields signed infinity; underflow produces subnormal representations or signed zero. Widening from `f32` to `f64` is exact.
4. **String and Byte Conversions**:
   - `str(bool)` formats `"true"` or `"false"`.
   - `bytes(str)` UTF-8 encodes the string into an immutable `bytes` buffer.
   - `str(bytes)` decodes an immutable `bytes` buffer into `str` using lossy UTF-8 decoding (malformed sequences replaced by `U+FFFD`). For fallible decoding, `ril/str::from_utf8` returns `Result<str, str>`.
   - `bytes(array: []u8)` copies a mutable or read-only `[]u8` into an immutable `bytes` buffer.
   - `[...buffer]` copies an immutable `bytes` buffer into a fresh mutable `[]u8` array. Neither conversion shares writable storage.

---

## 3. Relational, Equality, and Logical Operators

1. **Relational Operators (`<`, `<=`, `>`, `>=`)**:
   - Non-associative: chained comparisons like `a < b < c` are statically rejected.
   - Permitted only between homogeneous operands: `bool` (ordered `false < true`), numeric types, `str` (lexicographic Unicode scalar order), and `bytes` (lexicographical unsigned byte order).
2. **Equality Operators (`==`, `!=`)**:
   - Homogeneous: comparing different types is a static error.
3. **Logical Operators (`&&`, `||`)**:
   - Short-circuiting: `left && right` evaluates `right` only if `left` is `true`; `left || right` evaluates `right` only if `left` is `false`. Operands MUST be `bool`.

---

## 4. Range, Indexing, and Access Expressions

### 4.1 Ranges (`..`, `..=`)

```ril
let half_open = 0..3  -- yields 0, 1, 2
let inclusive = 0..=3 -- yields 0, 1, 2, 3
```

1. Ranges are non-associative expressions constructing range descriptors. Both bounds MUST have the identical integer type.
2. An integer range where $\text{start} > \text{end}$ is valid and denotes an empty range.

### 4.2 Sequence Indexing and Slicing (Arrays and Bytes)

1. **Direct Array Indexing (`arr[index]`)**:
   - Evaluates index as `int`.
   - An out-of-bounds index ($index < 0$ or $index \ge \text{len}$) MUST trigger a runtime panic (`panic: index out of bounds`).
2. **Safe Array Indexing (`arr?[index]`)**:
   - Returns `Option<T>` (`?T`). An out-of-bounds index evaluates to `None` without panicking.
3. **Slicing (`collection[start..end]`)**:
   - Yields a sub-slice. Slice bounds are clamped safely to collection bounds; out-of-range slice indices evaluate to an empty slice `[]` and NEVER panic.

### 4.3 Associative and Positional Indexing (Maps and Tuples)

1. **Map Indexing (`map[key]`)**:
   - Evaluates key `key: K` and returns an `Option<V>` (`?V`).
   - If the key exists, it evaluates to `Some(value)`. If the key is absent, it evaluates to `None` and NEVER panics.
2. **Map Entry Assignment (`map[key] = value`)**:
   - Inserts or replaces the entry at `key` with `value: V`.
3. **Map Compound Assignment**:
   - Compound assignments (`map[key] += 1`, `map[key] *= 2`) require an existing entry. If the key is absent from the map, it MUST trigger a runtime panic (`panic: Map compound assignment requires an existing entry`). To update safely with defaults, use library primitives `ensure` or `update`.
4. **Positional Tuple Indexing (`tuple.0`, `tuple.1`)**:
   - Positionally accesses fields of a tuple using 0-based decimal index notation. Indexing out of tuple bounds is a compile-time static error.

---

## 5. Pipeline Operators (`|>` and `!>`)

Ril replaces method-call syntax (UFCS) with two dedicated pipeline operators:

### 5.1 Linear Pipeline Operator (`|>`)

```ril
x |> f      -- desugars to: f(x)
x |> f(y)   -- desugars to: f(x, y)
```

1. **Data-First Convention**: `|>` passes the left-hand side expression as the first positional argument to the right-hand callable.
2. **Associativity and Chaining**: `|>` is left-associative and chainable: `x |> f |> g` evaluates to `g(f(x))`.
3. **Shared / Value Passing**: `|>` passes data as an ordinary value or read-only view. Passing a mutable location requiring `mut` via `|>` is a compile-time static error.

### 5.2 Mutating Pipeline Operator (`!>`)

```ril
mut_target !> Array::push(item)       -- desugars to: Array::push(mut mut_target, item)
mut_target !> Array::extend([1, 2])   -- desugars to: Array::extend(mut mut_target, [1, 2])
```

1. **LValue Requirement**: The left-hand side of `!>` MUST resolve to a valid mutable storage location (`AssignTarget`).
2. **Mut Forwarding**: `!>` passes the LHS as the first argument with an implicit `mut` borrow.
3. **Return Value**: The expression evaluates directly to the return value of the invoked function.
4. **Strict Single-Use Rule**: `!>` is strictly **non-associative and single-use**. Chaining `!>` with `!>` (e.g., `a !> f() !> g()`) or chaining `!>` with `|>` is a compile-time static error.
5. **Namespace Qualification and Scoped Imports**: Container-specific mutation functions belong to standard library modules (e.g., `ril/array`). Calls via `!>` MAY use type-qualified identifiers (`mut_target !> Array::push(item)`) or unqualified identifiers when locally imported into the enclosing block (`use ril/array::{push}`).

### 5.3 Pipeline and Closure Delimiter Boundaries

At the outer delimiter depth of an inline closure, `|>`, `!>`, and `??` immediately terminate the closure body. To embed a pipeline or fallback within a closure body, explicit parentheses or a block MUST be supplied:

```ril
users |> map \u -> {
    u.name |> \s -> "user: " + s
}
```

---

## 6. Accessor Expressions (`\.field`)

A lambda-prefixed dot introduces a first-class accessor closure for record field projection:

```ril
let get_name = \.name           -- desugars to: \x -> x.name
let get_city = \.addr.city      -- desugars to: \x -> x.addr.city
```

Accessor expressions can be passed directly as higher-order arguments to pipeline stages (e.g., `users |> map(\.name)`).

---

## 7. Error Handling Operators (`?` and `??`)

### 7.1 Postfix Error Propagation (`?`)

```ril
let val = fallible_op()?
let mapped = fallible_op() ? AppError::FromIo
```

1. **Unwrapping**: Applied to `Option<T>` or `Result<T, E>`. If the value represents success (`Some(v)` or `Ok(v)`), it unwraps to `v`.
2. **Early Return**: If the value represents failure (`None` or `Err(e)`), it early-returns from the enclosing function or closure.
3. **Error Mapping**: When followed by a mapper expression on the same line, the failure payload is transformed by the mapper before returning.
4. **Option-to-Result Bridge**: In a function returning `Result<T, E>`, applying `?` to `opt: ?T` accepts an error value expression or lazy supplier `opt ? error_expr`, converting `None` to `Err(error_expr)`.
5. **Unused Result Enforcement**: Expressions evaluating to `Result<T, E>` MUST NOT be discarded in non-tail positions or via semicolons. Discarding via `let _ = fallible()` is statically rejected.

### 7.2 Fallback and Recovery Operator (`??`)

```ril
let port = config["port"] ?? 8080
let name = result ?? \err -> "default"
let token = header ?? return Err("unauthorized")
```

1. **Right-Associative**: `a ?? b ?? c` evaluates as `a ?? (b ?? c)`.
2. **Option Fallback**: Applied to `Option<T>`, the right-hand operand MAY be a raw fallback value of type `T` or a supplier.
3. **Result Fallback Closure Requirement**: Applied to `Result<T, E>`, the right-hand operand **MUST be an error-consuming closure `\err -> ...`** or a diverging control transfer (`return`, `panic`, `break`, `continue`). Supplying a raw value fallback on a `Result` is statically prohibited to prevent silent error masking.


