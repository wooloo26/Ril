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
   - Dynamic assertion calls (`assert(...)`) and runtime panics (`panic(...)`). Total functions MUST rely on constructive propositional equality (`Eq<A, a, b>`, `Refl`) rather than dynamic runtime panic conditions.
   - Live mutable state reads, resource handle operations, and object identity comparisons.
3. **Capture Rules in `halt fn`**:
   - Capturing external immutable values requires `&{name}` and is permitted only if the captured value is admissible in halting computation.
   - Observing live mutable variables—even through read-only views—is strictly forbidden.
   - Captured capabilities cannot be erased.
4. **Halting Contract Restriction**:
   Contracts (`requires`, `ensures`) declared on `halt fn` MUST be purely halting expressions. They SHALL NOT invoke algebraic effects or declare mutable capability bounds.
5. **Lemma 1.1 (Strictly Positive Structural Decrement)**:
   Every recursive call in a `halt fn` MUST decrease an immutable, strictly positive inductive argument along a well-founded subterm relation. Traversed inductive links MUST be immutable. Arbitrary cyclic graphs or negative recursive occurrences CANNOT justify halting recursion.
6. **Negative Occurrence Ban**:
   Negative recursive types (e.g., `type Negative { Wrap(halt fn(Negative) -> never) }`) CANNOT be eliminated in halting or erased type computation, even by a syntactically non-recursive function.
7. **Subtyping and Callable Decay**:
   A `halt fn` MAY be used where an ordinary `fn` with matching parameter permissions is expected (losing the termination guarantee), but an ordinary `fn` CANNOT be supplied where a `halt fn` is required.

### 1.2 Halting Metatheory

**Theorem 1.1 (Strong Normalization)**:
Every well-typed expression $e$ composed exclusively of constructs admissible in `halt fn` terminates in a finite number of operational reduction steps to a canonical value. Divergence ($\bot$) is statically impossible.

**Theorem 1.2 (Confluence / Church-Rosser)**:
If a compile-time type expression reduces along distinct reduction paths $e \to^* e_1$ and $e \to^* e_2$, there exists an expression $e_3$ such that $e_1 \to^* e_3$ and $e_2 \to^* e_3$. Normal forms in halting evaluation are unique.

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
### 2.3 Operational Reduction of `match type`

Given a target type expression $T$ normalized to canonical form $\tau$:

$$
\operatorname{eval}(\text{match type } T \lbrace P_1 \to E_1, \dots, P_n \to E_n \rbrace )
$$

1. **Sequential Pattern Matching**: For each arm $i \in \lbrace 1, \dots, n\rbrace$ in linear declaration order:
   - Compute structural unification $\operatorname{unify}(P_i, \tau) \Rightarrow \theta$, where $\theta$ binds each `infer U` variable to its corresponding extracted sub-component in $\tau$.
   - If unification succeeds, the match expression immediately reduces to $\theta(E_i)$.
2. **Exhaustiveness and Fallthrough**: If no pattern matches and no fallback arm (`_`) is defined, type computation fails at compile time with a static type error.
3. **Dead Pattern Detection**: If arm $P_k$ is statically subsumed by preceding patterns $\bigcup_{j \lt k} P_j$, the compiler SHALL emit a static dead code error.

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
4. Runtime equality checks (`assert(a == b)`) do NOT construct `Eq` evidence.

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

**Theorem 3.1 (Zero-Cost Proof Transport)**:
Let $p : \operatorname{Eq}\langle A, a, b\rangle$ be proof evidence and let $e : T[a]$. The expression `rewrite p in e` is statically typed with $T[b]$. The operational evaluation satisfies:

$$
\operatorname{eval}(\operatorname{rewrite}\ p\ \operatorname{in}\ e) \equiv \operatorname{eval}(e)
$$

In bytecode compilation and machine code emission, proof rewriting generates zero executable instructions and incurs zero runtime memory overhead.

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

The definitions `Acc`, `WellFounded`, and `well_founded` specify user-defined accessibility patterns and are not prelude exports.

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

Polymorphic operations requiring parameterized behaviors SHALL be represented using **explicit operation records**:

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

1. **First-Class Value Representation**: Protocols SHALL be represented as ordinary first-class record schemas containing function fields.
2. **Explicit Parameter Passing**: Implementations and callers SHALL pass protocol instances explicitly as arguments or record fields, eliminating ambiguous resolution cascades, coherence conflicts, and orphan instance restrictions.
