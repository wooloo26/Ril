# 02. Lexical Structure

This chapter specifies the lexical elements of Ril source code, including character encoding, comments, identifiers, reserved keywords, and literal representations.

---

## 1. Source Text and Encoding

Ril source files MUST be encoded in **UTF-8**. Conforming compilers MUST accept valid UTF-8 byte streams and MUST reject ill-formed byte sequences at the lexical scanning stage.

A source file consists of a sequence of Unicode scalar values (characters in the ranges `U+0000` through `U+D7FF` and `U+E000` through `U+10FFFF`).

---

## 2. Comments and Whitespace

### 2.1 Comments

Ril supports single-line comments introduced by a double hyphen (`--`):

```ebnf
Comment       ::= "--" { LineCharacter }
LineCharacter ::= (* Any Unicode scalar except LF (U+000A) or CR (U+000D) *)
```

A comment begins with `--` and extends to the end of the current physical line. Comments have no syntactic significance and are discarded by the scanner, acting as a single whitespace boundary.

### 2.2 Whitespace

Whitespace characters include the space character (`U+0020`), horizontal tab (`U+0009`), and line terminators (LF `U+000A`, CR `U+000D`, and CRLF `U+000D U+000A`). Whitespace separates tokens but is otherwise insignificant, except where line terminators act as item and expression separators (see [§03 (Formal Grammar and Syntax)](03_formal_grammar_and_syntax.md)).

---

## 3. Identifiers and Naming Conventions

### 3.1 Identifier Syntax

```ebnf
Identifier         ::= IdentifierStart { IdentifierContinue }
IdentifierStart    ::= "_" | UnicodeLetter
IdentifierContinue ::= IdentifierStart | Digit
UnicodeLetter      ::= (* Any Unicode character in General Category 'Lu', 'Ll', 'Lt', 'Lm', or 'Lo' *)
Digit              ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
```

An identifier begins with an underscore `_` or a Unicode letter, followed by zero or more letters, digits, or underscores. A solitary underscore `_` is not an identifier; it is the reserved wildcard token.

### 3.2 Canonical Naming Conventions

Conforming Ril programs SHOULD adhere to the following normative conventions:
- **PascalCase** (`TypeIdentifier`): Types, type constructors, algebraic effect names, and sum type variant tags.
- **snake_case** (`variable_identifier`): Variables, constants, function names, record fields, and module names.

---

## 4. Keywords

### 4.1 Active Reserved Keywords

The following tokens are strictly reserved, MUST NOT be used as user-defined identifiers in any context, and possess active syntactic roles in the current grammar:

```
as       break    continue effect   else
erased   false    fn       for      if
in       infer    is       keyof    let
loop     match    module   mut      never
opaque   pub      return   rewrite  test
true     type     typeof   use      where
while    with
```

### 4.2 Future Reserved Keywords

The following tokens are strictly reserved for forward compatibility and future language extensions. They MUST NOT be used as user-defined identifiers in any context, but currently carry no active grammatical productions:

```
auto     const    decl     derive   macro
static   unsafe   yield
```

### 4.3 Contextual Keywords

Contextual keywords carry special syntactic meaning only within specific grammatical productions; in all other positions, they are parsed as ordinary identifiers:
- `resume`: Delimited continuation resumption expression within effect handlers.
- `super`: Relative module path navigation prefix.
- `halt`: Modifier immediately preceding the `fn` keyword denoting total halting functions.
- `lacks`: Row absence constraint operator within `where` clauses (`R lacks "label"`).
- `capture`: Environment capture state capability annotation (`&capture`).
- `scoped`: Lexical resource lifetime and cleanup modifier on `let` declarations (`let scoped`, `let scoped mut`).

---

## 5. Literals

### 5.1 Booleans

The boolean literal tokens are `true` and `false`, inhabiting the primitive type `bool`.

### 5.2 Numeric Literals

Ril supports integer and floating-point literals with optional numeric type suffixes.

```ebnf
NumericSuffix  ::= "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64"
FloatSuffix    ::= "f32" | "f64"
DecimalDigits  ::= Digit { [ "_" ] Digit }
HexDigits      ::= "0x" HexDigit { [ "_" ] HexDigit }
OctalDigits    ::= "0o" OctalDigit { [ "_" ] OctalDigit }
BinaryDigits   ::= "0b" BinaryDigit { [ "_" ] BinaryDigit }
ExponentPart   ::= ( "e" | "E" ) [ "+" | "-" ] DecimalDigits

IntegerLiteral ::= ( DecimalDigits | HexDigits | OctalDigits | BinaryDigits ) [ NumericSuffix ]
FloatLiteral   ::= DecimalDigits "." DecimalDigits [ ExponentPart ] [ FloatSuffix ]
```

#### Numeric Literal Rules and Ranges
1. **Underscores**: Underscores `_` are permitted between digits for visual readability and do not affect the literal value.
2. **Explicit Suffixes**: When a literal contains an explicit suffix, its static type is fixed to that exact type without contextual inference. The literal value MUST fit within the representable range of that type; an out-of-range literal is a compile-time static error.
3. **Unsuffixed Defaults**:
   - An unsuffixed integer literal defaults to `int` (an alias for `i32`) unless an expected type from a typed context (annotation, parameter, return type) guides inference to another integer type.
   - An unsuffixed floating-point literal defaults to `f64`.
4. **Arbitrary-Precision Integers**: Literals targeting the type `bigint` accept arbitrarily large integer magnitudes without fixed-width boundary limitations.

| Type | Description / Range | Suffix | Default Context |
| :--- | :--- | :--- | :--- |
| `i8` | Signed 8-bit integer: $-128$ to $127$ | `i8` | Expected type |
| `i16` | Signed 16-bit integer: $-32768$ to $32767$ | `i16` | Expected type |
| `i32` / `int` | Signed 32-bit integer: $-2^{31}$ to $2^{31}-1$ | `i32` | **Default integer** |
| `i64` | Signed 64-bit integer: $-2^{63}$ to $2^{63}-1$ | `i64` | Expected type |
| `u8` | Unsigned 8-bit integer: $0$ to $255$ | `u8` | Expected type |
| `u16` | Unsigned 16-bit integer: $0$ to $65535$ | `u16` | Expected type |
| `u32` | Unsigned 32-bit integer: $0$ to $2^{32}-1$ | `u32` | Expected type |
| `u64` | Unsigned 64-bit integer: $0$ to $2^{64}-1$ | `u64` | Expected type |
| `bigint` | Arbitrary-precision signed integer | None | Expected type |
| `f32` | IEEE 754 binary32 single-precision float | `f32` | Expected type |
| `f64` | IEEE 754 binary64 double-precision float | `f64` | **Default float** |

### 5.3 Strings and Interpolation

Strings in Ril represent immutable UTF-8 scalar sequences inhabiting the type `str`.

```ebnf
StringLiteral      ::= '"' { StringCharacter | StringEscape | Interpolation } '"'
StringCharacter    ::= (* Any Unicode scalar except '"', '\', '{', or '}' *)
StringEscape       ::= "\" ( "n" | "r" | "t" | "\" | '"' | "0" | "{" | "}" | "u{" HexDigit { HexDigit } "}" )
Interpolation      ::= "{" Expression [ ":" FormatSpec ] "}"
FormatSpec         ::= [ "0" DecimalDigits ] ( "x" | "X" | "b" | "o" ) | "0" DecimalDigits | "." DecimalDigits "f"
PlainStringLiteral ::= '"' { StringCharacter | StringEscape } '"'
RawStringLiteral   ::= "`" { RawCharacter } "`"
RawCharacter       ::= (* Any Unicode scalar except '`' *)
```

#### String Escape Sequences
- `\n`: Line Feed (`U+000A`)
- `\r`: Carriage Return (`U+000D`)
- `\t`: Horizontal Tab (`U+0009`)
- `\\`: Backslash (`U+005C`)
- `\"`: Double Quote (`U+0022`)
- `\0`: Null Character (`U+0000`)
- `\{`: Literal Opening Brace (`U+007B`)
- `\}`: Literal Closing Brace (`U+007D`)
- `\u{XXXX}`: Unicode scalar value given by 1 to 6 hexadecimal digits.

#### String Interpolation and Format Specifiers
1. **Expression Embedding**: Within `"..."`, an unescaped brace `{expr}` evaluates `expr` and formats its string representation into the resulting string.
2. **Format Specifiers**: A colon following the expression introduces an optional format specifier `{expr:spec}`:
   - `.Nf`: Fixed decimal precision rounded to $N$ decimal places (e.g., `{3.14159:.2f}` yields `"3.14"`).
   - `x` / `X`: Hexadecimal formatting (lowercase / uppercase).
   - `b`: Binary base formatting.
   - `o`: Octal base formatting.
   - `0N`: Zero-padding to minimum width $N$.
3. **Prohibition of Implicit Nominal Unpacking**: A single-payload nominal wrapper (e.g., `type UserId(str)`) does NOT implicitly unpack in string interpolation. Accessing and formatting a nominal wrapper's underlying value within string interpolation MUST be performed explicitly using `raw(wrapper)` (e.g., `"{raw(uid)}"`). Directly embedding a nominal wrapper in string interpolation without `raw()` is a compile-time static error (`NominalInterpolationRequiresRawError`).

#### Raw Strings
Enclosed in backticks (`` `...` ``), raw strings treat backslashes and braces as literal characters. No escape sequences or interpolation expressions are recognized.

### 5.4 Bytes and Byte String Literals

1. **ASCII Byte Literal**: `b'c'` denotes an individual unsigned 8-bit byte inhabiting `u8`. Permitted escapes are `\n`, `\r`, `\t`, `\\`, `\'`, `\"`, `\0`, and `\xHH` (hexadecimal byte).
2. **Immutable Byte Buffer Literal**: `b"..."` denotes an immutable byte sequence inhabiting `bytes`.

```ebnf
ByteLiteral       ::= "b'" ( ByteCharacter | ByteEscape ) "'"
ByteCharacter     ::= (* Any ASCII character except ''', '\', LF, or CR *)
ByteEscape        ::= "\" ( "n" | "r" | "t" | "\" | "'" | '"' | "0" | "x" HexDigit HexDigit )
ByteStringLiteral ::= 'b"' { ByteStringCharacter | ByteEscape } '"'
```

### 5.5 Regular Expression Literals

Regular expression literals are prefixed with `reg"` and inhabit the standard library regular expression matcher type:

```ebnf
RegexLiteral   ::= 'reg"' { RegexCharacter } '"'
RegexCharacter ::= "\" UnicodeScalar | (* Any Unicode scalar except '"' or '\' *)
```

### 5.6 Unit and Never Literals

- The empty tuple `()` denotes the sole value of the unit type `()`.
- The bottom type `never` represents uninhibited computations that diverge or panic, and possesses no runtime value literal.
