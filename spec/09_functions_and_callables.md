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

## 2. Parameter Modes, Defaults, and Call Arguments

```ebnf
Parameter     ::= [ "mut" | "erased" ] Identifier [ ":" TypeExpression ] [ "=" Expression ]
ParameterList ::= Parameter { "," Parameter } [ "," ]

Argument      ::= [ Identifier ":" ] ( "mut" AssignTarget | Expression )
Arguments     ::= Argument { "," Argument } [ "," ]
ArgumentsCall ::= "(" [ Arguments ] ")"
```

### 2.1 Parameter Modes and Caller Obligations

1. **Shared Read-Only (Default)**: `x: T` passes a value or safely shared managed reference. It is contravariant in callable subtyping.
2. **Borrowed Mutable Location**: `mut x: T` grants in-place write access to caller storage.
   - **Reference Type Precondition**: The parameter type `T` MUST be a heap-allocated reference type (record, array, map, tuple, or sum type). Declaring `mut` on value types (integers, floats, booleans, unit, never, str, bytes) is a compile-time static error (`ValueTypeMutableBorrowError`).
   - **Caller LValue Contract**: Callers supplying arguments to `mut` parameters MUST explicitly prefix the argument with `mut` (e.g., `f(mut x)`) or employ the mutating pipeline operator (`x !> f()`). Passing rvalues, temporaries, or expressions without addressable storage is a compile-time static error.
   - **Definite Mutation Invariant (`UnusedMutError`)**: Any parameter declared with `mut` MUST undergo at least one reachable write operation along an executable control-flow path. An unmutated `mut` parameter is a compile-time static error.
3. **Erased Parameter**: `erased x: T` marks parameters used purely for compile-time indexing or proofs. Erased parameters are eliminated during compilation and have zero runtime footprint.
4. **Cross-Argument Disjointness Invariant (Law of Exclusivity)**:
   > **Normative Invariant**: For every argument $a_i$ bound to a `mut` parameter, its storage path MUST be pairwise disjoint from every other argument $a_j$ ($j \ne i$) supplied in the identical call frame:
   >
   > $$\forall i \in \mathop{\mathrm{MutArgs}}, \ \forall j \in \mathop{\mathrm{AllArgs}} \setminus \lbrace i\rbrace , \quad \mathop{\mathrm{Path}}(a_i) \cap \mathop{\mathrm{Path}}(a_j) = \emptyset$$
   >
   - Passing overlapping paths to two or more `mut` parameters is rejected with `E0523: MutMutAliasingConflictError`.
   - Passing overlapping paths to a `mut` parameter and a read-only parameter is rejected with `E0524: ReadMutAliasingHazardError`.

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

## 3. Closures (Lambdas) and Field Accessors

```ebnf
LambdaHead        ::= "\" [ ParameterList ] "->"
LambdaExpr        ::= LambdaHead InlineLambdaBody
InlineLambdaBody  ::= LogicalOrExpr | AssignTarget AssignmentOp LogicalOrExpr
AccessorExpr      ::= "\" "." Identifier { "." Identifier }
```

1. **Lexical Scope (No Hoisting)**: Closures are strictly lexical values and MUST be defined before use.
2. **Automatic Signature Inference**:
   Closures automatically infer parameter types, return types, algebraic effects, and environment capture capabilities (`&mut`, `&^mut`, `&capture`, `&{var}`, `&{mut var}`, `&{^mut var}`) from their body expressions. Publishing a writable capture is separately checked on the creating callable (Chapter 11, §3.1).
3. **Delimited Inline Body Boundary Invariant**:
   At the outermost nesting depth of an unparenthesized `InlineLambdaBody`, pipeline operators (`|>`, `!>`) and fallback operators (`??`) immediately delimit and terminate the closure body.
4. **Field Accessor Expressions (`\.field`)**:
   `\.field` desugars operationally to an anonymous pure projection closure `\obj -> obj.field`.

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

### 5.1 Theorem (Automatic Effect and Capability Forwarding)

Let $f$ be a higher-order function receiving a callable parameter $g: \text{fn}(P) \to R \ @\mathcal{E}_g \ \mathbin{\And}\mathcal{S}_g$. If $f$ invokes $g$ within its evaluation body:
1. **Implicit Polymorphic Forwarding**: The function signature of $f$ requires no explicit effect type variables or effect annotations to forward $g$'s effects.
2. **Call-Site Set Union**: At every call site $f(v, c)$, the effective effect requirement of the call expression is:

   $$\mathcal{E}_{\text{call}} = \mathcal{E}_f \cup \mathcal{E}_c$$

   where $\mathcal{E}_f$ denotes $f$'s intrinsically declared effects, and $\mathcal{E}_c$ denotes the concrete effects inferred for argument $c$.
3. **Purity Conservation**: If a concrete callable argument $c$ is purely functional ($\mathcal{E}_c = \emptyset$), the call site incurs strictly zero additional effect obligations.
4. **State Capability Forwarding**: Callback state obligations are forwarded with their binding identities and origin summaries intact. When a callback or callee retains writable aliases to external state `x`, the enclosing call retains `&{^mut x}`; it MUST NOT weaken that requirement to `&{mut x}` or `&capture` alone. Parameter-origin obligations are substituted with actual argument origins. Local discharge and explicit interface abstraction follow Chapter 11; merely forwarding a mutation-only callback does not introduce retained sharing.
