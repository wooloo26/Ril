# 12. Type Computation and Proofs

This chapter specifies compile-time type computation, total halting functions (`halt fn`), structural and well-founded induction, propositional equality proofs (`Eq`), type matching, and explicit operation protocols.

---

## 1. Halting Functions (`halt fn`)

A halting function is a total, mathematically sound function guaranteed to terminate normally for every input admitted by its signature:

```ebnf
HaltFunctionDecl ::= [ "pub" ] "halt" "fn" Identifier [ GenericParameters ] "(" [ ParameterList ] ")"
                     [ "->" TypeExpression ] { ContractArgument } [ WhereClause ] Block
```

```ril
type Nat { Zero, Succ(Nat) }

halt fn add(left: Nat, right: Nat) -> Nat {
    match left {
        Zero -> right,
        Succ(rest) -> Nat::Succ(rest |> add(right)),
    }
}
```

### 1.1 Halting Body Invariants

1. **Permitted Constructs**:
   - Immutable bindings (`let`).
   - Constructor applications and projections.
   - Exhaustive pattern matching.
   - Total arithmetic primitives with statically verified non-overflow/non-zero preconditions.
   - Applications of other `halt fn` callables.
2. **Prohibited Constructs**:
   - Unbounded loops (`loop`, `while`).
   - Mutable bindings (`let mut`) and parameter mutations (`mut`).
   - Algebraic effect invocations (`@Effect`) and effect handlers (`with`).
   - Foreign host declarations (`decl`).
   - Live mutable state reads, resource handle operations, and object identity comparisons.
3. **Capture Rules in `halt fn`**:
   - Capturing external immutable values requires `&{name}` and is permitted only if the captured value is admissible in halting computation.
   - Observing live mutable variables—even through read-only views—is strictly forbidden.
   - Captured capabilities cannot be erased.
4. **Strictly Positive Structural Induction**:
   - Every recursive call in a `halt fn` MUST decrease an immutable, strictly positive inductive argument.
   - Traversed inductive links MUST be immutable. Arbitrary cyclic graphs or negative recursive occurrences CANNOT justify halting recursion.
5. **Prohibition of Negative Recursive Elimination**:
   - Negative recursive types (e.g., `type Negative { Wrap(halt fn(Negative) -> never) }`) CANNOT be eliminated in halting or erased type computation, even by a syntactically non-recursive function. This rule prevents Girard's / Curry's paradox in compile-time reduction.
6. **Subtyping and Callable Decay**:
   A `halt fn` MAY be used where an ordinary `fn` with matching parameter permissions is expected (losing the termination guarantee), but an ordinary `fn` CANNOT be supplied where a `halt fn` is required.

---

## 2. Compile-Time Type Computation and Type Matching

### 2.1 Erased Type Computation

Bindings and functions producing universe values (`Type<u>`) are erased and evaluate at compile time. Initializers of type-valued expressions MUST be pure, terminating halting computations.

### 2.2 Type Structure Matching (`match type`)

```ebnf
TypeMatch    ::= "match" "type" TypeExpression "{" TypeMatchArm { "," TypeMatchArm } [ "," ] "}"
TypeMatchArm ::= TypePattern "->" TypeExpression
TypePattern  ::= "infer" Identifier | "_" | "never" | LiteralType | TypePatternRef
               | "?" TypePattern | "[" "]" TypePattern
               | "(" TypePattern "," [ TypePattern { "," TypePattern } [ "," ] ] ")"
               | "(" ")" | RecordTypePattern | FunctionTypePattern
```

```ril
type Column<T>(T)
type Cell<C> = match type C {
    Column<infer T> -> T,
    _ -> never,
}
```

1. **Structural Inspection**: `match type` inspects visible compile-time type structure in erased contexts.
2. **Component Binding (`infer U`)**: The `infer` keyword binds extracted sub-component types.
3. **Sequential Reduction**: Arms are evaluated in declaration order. An arm reduces only when its pattern matches and all preceding arms are proven disjoint.
4. **Structural Matching Constraints**:
   - Matching evaluates type structure, NOT subtyping or inhabitation.
   - There is NO implicit distribution over literal unions.
   - Higher-rank and dependent callable binders are NOT decomposed by type patterns.
   - All match arms MUST produce compatible sorts.
5. **Opaque Boundary Invariant**: An opaque type's underlying representation is NEVER exposed to `match type` outside its defining module.

---

## 3. Propositional Equality and Proof Rewriting

The standard prelude defines the propositional identity type family `Eq`:

```ril
type Eq<A, a: A, b: A> {
    Refl<A, x: A> -> Eq<A, x, x>,
}
```

### 3.1 Reflexivity and Definitional Equality

1. The constructor `Refl` constructs equality evidence if and only if its index arguments are **definitionally equal** ($a \equiv b$).
2. Cumulative universe typing does not identify distinct types for `Refl`.
3. Incompatible indices (e.g., `Eq<int, 1, 2>`) CANNOT construct `Refl` and produce a compile-time static error.
4. Runtime equality checks (`assert a == b`) do NOT construct `Eq` evidence.

### 3.2 Proof Rewriting (`rewrite ... in`)

```ebnf
RewriteExpr ::= "rewrite" ( QualifiedName | "(" Expression ")" ) "in" Expression
```

```ril
halt fn right_zero(n: Nat) -> Eq<Nat, {n |> add(Nat::Zero)}, n> {
    match n {
        Zero -> Refl,
        Succ(k) -> rewrite (k |> right_zero) in Refl,
    }
}
```

1. Given evidence `proof: Eq<A, a, b>`, the expression `rewrite proof in expr` replaces occurrences of `a` with `b` in the expected type of `expr` and transports the term across the equality.
2. `rewrite` is purely static: it produces zero runtime instructions or casts.

### 3.3 Erased Evidence Parameters

1. Parameters marked `erased` (e.g., `erased proof: Eq<A, a, b>`) exist exclusively for static type and proof verification and are completely stripped from runtime code generation.
2. **Erased Argument Calling Restrictions**:
   An expression passed to an erased parameter MUST be a halting expression or a previously evaluated immutable evidence binding. Ordinary runtime functions returning proofs CANNOT be called directly in erased argument positions (`fake() |> accept` is statically rejected).
3. **Runtime Execution of Evidence Initializers**:
   The binding that acquires runtime evidence executes at runtime, including its effects, panics, or divergence; its execution CANNOT be erased as an unused proof.

---

## 4. Well-Founded Recursion and Accessibility

To enable sound termination proofs for recursive algorithms whose arguments decrease along well-founded relations rather than structural subterms, Ril patterns support accessibility:

```ril
type Acc<A, R: fn(A, A) -> Type, x: A> {
    Access<A, R: fn(A, A) -> Type, x: A>(
        descend: halt fn(y: A, erased smaller: R<y, x>) -> Acc<A, R, y>,
    ) -> Acc<A, R, x>,
}

type WellFounded<A, R: fn(A, A) -> Type> = halt fn(x: A) -> Acc<A, R, x>

halt fn well_founded<A, R: fn(A, A) -> Type, P: fn(A) -> Type>(
    value: A,
    accessible: Acc<A, R, value>,
    step: halt fn(
        x: A,
        recur: halt fn(y: A, erased smaller: R<y, x>) -> P<y>,
    ) -> P<x>,
) -> P<value> {
    match accessible {
        Access(descend) -> value |> step(\y, erased smaller -> {
            y |> well_founded::<A, R, P>((y |> descend(smaller)), step)
        }),
    }
}
```

*Note*: `Acc`, `WellFounded`, and `well_founded` are standard pattern models; they are user-defined type computation patterns rather than prelude exports.

---

## 5. User-Defined Record Operations and Protocols

### 5.1 Type-Level Record Utilities

Using mapped types and `keyof`, developers can construct standard structural utilities:

```ril
type Pick<T: Record, K> where K <: keyof T = {
    [k in keyof T if k in K]: T[k],
}

type Omit<T: Record, K> where K <: keyof T = {
    [k in keyof T if !(k in K)]: T[k],
}

type Patch<T: Record> = {
    [k in keyof T]: ?T[k],
}
```

### 5.2 Explicit Operation Protocols

Ril deliberately omits ad-hoc type classes and implicit instance resolution. Polymorphic operations requiring custom behaviors rely on **explicit operation records**:

```ril
type Ordering { Less, Equal, Greater }
type Order<T> = { compare: fn(T, T) -> Ordering }

fn compare_int(a: int, b: int) -> Ordering {
    if a < b { Ordering::Less }
    else if a > b { Ordering::Greater }
    else { Ordering::Equal }
}

let int_order: Order<int> = .{ compare: compare_int }
```

1. **Zero Magic**: Protocols are ordinary first-class record schemas containing function fields.
2. **Explicit Passing**: Callers pass protocol instances explicitly, eliminating ambiguous resolution, coherence conflicts, or orphan rules.
