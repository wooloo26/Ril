# 09. Functions and Callables

This chapter specifies the declaration, evaluation, type inference, parameter modes, and higher-order composition of functions and closures in Ril.

---

## 1. Named Function Declarations and Hoisting

```ebnf
FunctionSignature ::= [ "halt" ] "fn" Identifier [ GenericParameters ] "(" [ ParameterList ] ")"
                     [ "->" TypeExpression ] { ContractArgument } [ WhereClause ]
FunctionDecl      ::= [ "pub" ] FunctionSignature Block
```

### 1.1 Newspaper Ordering (Hoisting Invariant)

Named functions declared at module scope possess module-wide visibility and are **hoisted across the entire module**:
- Callers MAY be defined physically before callees in the source text.
- Mutual recursion between named functions is supported without forward declarations.

### 1.2 Signature Layout and Dedicated Lines

In a function declaration, the return type annotation `-> ReturnType` and each effect or state capability annotation (`@Effect`, `&mut`, `&^mut`, `&capture`) MAY appear on dedicated separate lines following the parameter list:

```ril
pub fn process_data(
    id: int,
    payload: str,
)
    -> Result<str, str>
    @Io
    &mut
{
    -- body
}
```

### 1.3 Return Type Inference and Row Completion

1. **Full Return Type Inference (`-> _`)**:
   A function signature MAY specify `-> _`, directing the compiler to infer the complete static return type from the function body's final expression.
2. **Partial Row Completion (`-> { field: T, .._ }`)**:
   A function signature MAY declare required fields followed by `.._`, requiring the specified fields while inferring all additional fields and methods from the return expression into a concrete closed record type.
3. **Type Extraction via `typeof`**:
   The `typeof` operator applied to an unexecuted call expression extracts the inferred return type into an explicit type alias without duplicate signatures:
   ```ril
   pub type Counter = typeof make_counter(0)
   ```

---

## 2. Parameter Modes, Defaults, and Named Arguments

```ebnf
Parameter     ::= [ "mut" | "erased" ] Identifier [ ":" TypeExpression ] [ "=" Expression ]
ParameterList ::= Parameter { "," Parameter } [ "," ]
```

### 2.1 Parameter Modes

1. **Shared Read-Only (Default)**: `x: T` passes a value or safely shared managed reference.
2. **Borrowed Mutable Location**: `mut x: T` grants in-place write access to caller storage.
3. **Erased Parameter**: `erased x: T` marks parameters used purely for compile-time indexing or proofs. Erased parameters are eliminated at runtime and possess zero runtime representation.

### 2.2 Default Expressions and Evaluation Order

1. **Purity Invariant**:
   Default parameter expressions MUST be strictly pure expressions:
   - They CANNOT invoke algebraic effects (`@Effect`);
   - They CANNOT read or mutate external mutable state;
   - They carry no effect annotations and contribute no effects to the function signature.
2. **Evaluation Sequencing**:
   - Explicit arguments evaluate once, strictly left-to-right in source order, before any omitted defaults.
   - Omitted defaults evaluate afterwards in declaration order. A default expression MAY read earlier parameters and their computed defaults, but CANNOT reference subsequent parameters.
3. **Prohibition of Defaults on Mutable Parameters**:
   A mutable parameter (`mut param: T`) MUST NOT declare a default expression. Defaults cannot manufacture writable caller storage locations.

### 2.3 Named Arguments

1. Callers MAY supply arguments using parameter name labels: `f(delta: 2, base: 10)`.
2. Named arguments are order-independent at the call site, but they associate with parameter bindings without altering the left-to-right evaluation order of explicit argument expressions.
3. Supplying an argument both positionally and by name is a compile-time static error.

### 2.4 Tuple Argument Spreading

A tuple value MAY be spread into an argument list using `...tuple`:
```ril
let coords = (10, 20)
draw_point(...coords)
```
1. Tuple elements are supplied positionally in tuple index order.
2. Tuple spreads CANNOT supply `mut` arguments or manufactured writable locations.

---

## 3. Closures (Lambdas)

```ebnf
LambdaHead ::= "\" [ ParameterList ] "->"
LambdaExpr ::= LambdaHead InlineLambdaBody
```

1. **Lexical Scope (No Hoisting)**: Closures are strictly lexical values and MUST be defined before use.
2. **Automatic Signature Inference**:
   Closures automatically infer parameter types, return types, algebraic effects, and environment capture capabilities (`&mut`, `&capture`, `&{var}`, `&{mut var}`) from their body expressions.

---

## 4. Trailing Closures

When a function call's final parameter is a callable (closure), the closure expression MAY be placed outside the call parentheses:

```ril
apply(21) \x -> x * 2        -- equivalent to: apply(21, \x -> x * 2)
run_action \-> 100           -- equivalent to: run_action(\-> 100)
```

If the call passes no other preceding arguments, the empty parentheses `()` MAY be omitted entirely: `run_scoped \x -> x * 2`.

---

## 5. Higher-Order Functions and Automatic Effect Forwarding

A central feature of Ril's effect system is **Automatic Effect Forwarding**:

```ril
fn apply<T, U>(value: T, f: fn(T) -> U) -> U {
    f(value) -- automatically infers and forwards effects of f
}
```

1. **Zero Function-Coloring Friction**:
   Higher-order named functions (`fn`) do NOT require explicit effect type parameters or return effect annotations to forward callback effects. Invoking a callable parameter automatically infers that callback's effects and propagates them to the caller.
2. **Explicit vs. Forwarded Effects**:
   - If a higher-order function performs its own explicit effect operations (e.g., `Log::write(...)`), those operations MUST be declared in its signature (`@Log`).
   - The effects of invoked callback parameters are added transparently to the resulting effect set at the call site.
