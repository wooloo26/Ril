# 12. Type Computation and Totality

This chapter defines closure-based static computation, strict halt boundaries, total runtime functions, finite type programming, and controlled graph transformations. The historical filename is retained for existing chapter links; proof-assistant facilities are not core syntax.

---

## 1. Static Closures and Type Values

```ril
halt type Box = \T -> type[{ value: T }]
type IntBox = Box(type[int])

halt type IsArray = \T: Type -> match type T {
    []infer U -> true,
    _ -> false,
}

halt type Element = \T: Type -> match type T {
    []infer U -> U,
    _ -> T,
}
type ElementOf<T> = Element(type[T])
```

A static callable binding is introduced by `[halt] type Name = Expression`; it uses ordinary closure syntax and infers its static result sort. It is not declared using fn, and need not repeat `-> Type`. Result inference permits static predicates and Result-producing builders. This does not make a bool-returning helper a runtime callable.

`type[TypeExpression]` constructs a Type value in an expression with an explicit quotation boundary. Runtime data, static Type descriptions, and static callable sorts are separated as in Chapter 04. Type functions execute only statically. `typeof` never executes a runtime expression or lifts runtime contents.

Static callable bindings use closure parameters only and ordinary calls such as Box(type[int]); a left-side generic header or Box<int> call is rejected for callable bindings. Data/schema aliases retain generic application. First-class static callable aliases and composition results are permitted under Chapter 06 initialization checks. Computed type aliases consume Type-valued expressions, while direct data/schema syntax remains available.

Higher-order sorts are `[halt] type(S1,...,Sn) -> R`, always including the result sort. These have no runtime representation. Ordinary static callables cannot be promoted to halt, and halt values may be forgotten to ordinary; the binding and its initializer provenance remain checked.

## 2. Two Strict Call Families

1. A halt type closure MUST invoke only certified halt static closures and sealed static primitives/data constructors. It MUST NOT invoke ordinary type closures, fn, or halt fn.
2. A halt fn MUST invoke only certified halt runtime callables and sealed runtime primitives/data constructors. It MUST NOT execute ordinary fn or static callables. This includes callbacks, defaults, implicit operations, and indirect/aliased calls.
3. The distinction is between execution families, not textual nesting. A runtime function's signature, generic constraints, local type annotations, and type declarations are elaborated by the static checker. In a halt fn or halt type declaration these elaboration dependencies MUST all be halt-admissible. Ordinary type computation is forbidden there, even in an apparently dead branch or after a successful cached evaluation.
4. Direct structural aliases and data constructors need no halt modifier; their actual elaboration and default-value dependencies are checked transitively. Aliases, imports, type reflection, stored callable interfaces, and caches MUST NOT launder an ordinary computation into a halt dependency. Admission metadata is separate from structural type equality and retains source applications even if normalization, phantom parameters, or dead-code elimination would erase their final contribution.
5. Signature elaboration using halt type is permitted for halt fn and is not a cross-family runtime call. A runtime halt fn cannot be passed as a static callback, nor can a static closure become a runtime callback.
6. Anonymous closures checked against a certified callable context require independent totality verification. Merely naming an ordinary declaration inside such a context does not promote it. Recursive callbacks are checked jointly with their callers, without circular assumptions.

```ril
halt type Box = \T -> type[{ value: T }]
type OrdinaryBox = \T -> type[{ value: T }]

halt fn accept(value: Box(type[int])) -> int { value.value }
-- halt fn reject(value: OrdinaryBox(type[int])) -> int { value.value }
-- STATIC ERROR: ordinary static dependency in halt signature

halt fn runtime_identity(n: int) -> int { n }
-- halt type Wrong = \n: int -> runtime_identity(n)
-- STATIC ERROR: static-to-runtime invocation

halt fn ignore<T>(value: T) -> int { 0 }
fn ordinary_value() -> int { 1 }
fn ordinary_caller() -> int { ignore(ordinary_value()) }
-- halt fn rejected_caller() -> int { ignore(ordinary_value()) }
-- STATIC ERROR: argument evaluation invokes an ordinary runtime callable
```

Implicit erasure of generic binders never erases required evaluation of ordinary arguments, payloads, defaults, or factory calls. An unused argument remains subject to the caller's halt boundary.

## 3. Ordinary Type Computation and Project Policy

Direct-lambda static bindings have recursive item visibility and SCC checking (Chapter 06). Callable aliases/composition initializers and let captures retain lexical initialization order; they cannot create eager recursive initialization cycles.

An unmarked `type Name = \...` is a pure static computation without a guaranteed normal return. It MAY use general recursion, loops, and ordinary static callbacks. It remains subject to stage, visibility, sort, type-safety, and existing state rules. Frame-local scalar/ordinary-value mutation can obey existing local purity; Type descriptions and static descriptor containers remain immutable. External mutable state, effects, I/O, target-dependent observation, and runtime function execution are forbidden.

Chapter 10 @Div/Fuel rules apply to runtime callables. Static closures record potential divergence through ordinary versus halt static qualification and compiler budgets; they do not infer runtime @Div and cannot execute a runtime Fuel handler. This stage rule does not alter runtime effect inference.

Ordinary type evaluation can finish with a valid result, report a static computation failure, or exceed a compiler resource budget. No runtime panic-catching or @Panic effect is introduced. A compile-time panic becomes a compilation diagnostic; no type is produced by failure.

Implementations MUST support finite, configurable evaluation limits and cancellation for static computation, including ordinary recursion, graph construction, and diagnostics. Exhaustion reports the pending computation and source trace, not a proof of nontermination. No implementation may choose an arbitrary fallback type.

A project lint MAY allow, warn on, or deny ordinary type closure declarations/usages. It does not define halt semantics, permit a forbidden dependency, or disable compiler resource enforcement. An unmarked closure is not halt merely because its body appears simple. Ordinary successful results can be used in ordinary runtime declarations; strict halt declarations reject their elaboration dependency provenance.

## 4. Halt Normal-Return Guarantee

Both halt families MUST terminate normally on every input in their admitted domain in the idealized abstract machine. Normal None/Err results are allowed; language-level panic and divergence are not. Physical memory exhaustion or external process termination is an implementation resource failure, not permission to ignore a language-specified bound.

Halt computation permits immutable bindings, certified constructor/projection operations, exhaustive matching, verified arithmetic, certified finite traversal, and same-family halt calls. Unbounded loop/while, let mut, mutable parameter operations, effect invocation/handling, live mutable reads, panic, assert, and uncertified callbacks are forbidden.

Every implicit operation is included: parameter/field defaults, formatting, equality, iterators, conversions, indices, string concatenation, array spread, and capacity growth. A language-specified maximum capacity of 2^31-1 remains a semantic bound. Builders with uncertain legality or capacity return Result; static rejection is not a halt closure's normal return path.

### 4.1 Finite Termination Analysis

The compiler SHALL use a finite conservative analysis incorporating:

- Immutable strictly positive subterms from stable finite inductive values.
- Bounded integer/length decrease, constant intervals, simple path conditions, and a finite set of difference relations; each arithmetic operation must also be safe.
- Lexicographic measures and whole recursive SCC checks, not only immediate self calls.
- Verified subterm, length, and stability summaries exported with helper interfaces. Unchecked user assertions of termination are not accepted.
- Certified finite higher-order traversals that retain callback progress information. Halt on a helper alone does not imply its output shrinks.

Recursive callable flow MUST be tracked through arguments, opaque type-member packages, operation records, closure captures, returned values, and aliases. A function currently being certified in a recursive group cannot be treated as an independently certified halt callback merely because it is stored behind a halt callable signature. Erasure and opening a hidden type MUST retain the runtime callable's recursive origin. If this indirect flow has no verified progress measure, the halt declaration is rejected.

```ril
halt type Nest = \T: Type, depth: int -> {
    if depth <= 0 { T }
    else {
        let element_type = Nest(T, depth - 1)
        type[[]element_type]
    }
}

halt fn countdown(n: int) -> int {
    if n <= 0 { 0 } else { countdown(n - 1) }
}

halt fn safe_increment(n: int) -> ?int {
    if n == 2147483647 { None } else { Some(n + 1) }
}
```

The decrement branches have a nonnegative lower bound and safe strict decrease. Wrapping subtraction without a terminating base case is not progress. Unknown higher-order recursion or repeated simplification without a certified measure is rejected in halt code. A supplied finite fuel may return an explicit unfinished result; it changes the original unbounded computation's domain or result semantics.

### 4.2 Stable Values and Induction

Read-only handles, deep freezing, and finite acyclic inductive structure are different facts. Immut<T> and clone_immut do not remove cycles. Runtime structural recursion requires stable positive links and a genuinely well-founded domain.

Intrinsically immutable positive constructor families can be certified. General graphs use the standard opaque `Acyclic<T>` wrapper, produced only by controlled constructors or a validating, isolating/freezing runtime operation returning Result. Its certificate covers the region actually read/traversed and propagates along verified immutable subterms. New constructions, callbacks, and helper results require independent source/size summaries; they are not automatically input subterms. External callers of opaque types use only public certified interfaces.

Negative recursive executable values cannot be eliminated by halt computation merely because their object graph is acyclic. The restriction covers runtime values and user static descriptor values. Finite inspection of negative positions in a Type metadata graph does not invoke those positions and is a separate operation.

```ril
type Bad { Wrap(halt fn(Bad) -> int) }
-- Reject: an indirect loop can be encoded through Wrap(run)
-- halt fn run(b: Bad) -> int { match b { Wrap(f) -> f(b) } }
```

Hiding the callback argument type does not remove this obligation:

```ril
type CallbackBox = {
    opaque type Arg,
    argument: Arg,
    invoke: halt fn(Arg) -> int,
}
halt fn call_box(box: CallbackBox) -> int {
    let .{ argument, invoke } = box
    invoke(argument)
}
-- Reject the recursive declaration below:
-- halt fn reenter(k: halt fn(CallbackBox) -> int) -> int {
--     k(.{
--         Arg: type[halt fn(CallbackBox) -> int],
--         argument: k,
--         invoke: reenter,
--     })
-- }
-- reenter(call_box) would cycle through reenter -> call_box -> reenter.
```

The independently verified call_box is permitted. The proposed reenter cannot use its own provisional certification to construct the callback package. An acyclic heap or an Acyclic wrapper cannot certify this executable cycle.

Halting properties are specification obligations, not a completed metatheoretic proof. Implementations must verify their trusted primitives, classification, type-relation algorithms, and totality analysis independently.

## 5. Type Matching, Finite Tuples, and Builders

```ebnf
TypeMatch    ::= "match" "type" TypeExpression
                 "{" TypeMatchArm { "," TypeMatchArm } [ "," ] "}"
TypeMatchArm ::= TypePattern "->" Expression
```

When the target is a static Type variable, its descriptor is inspected; bare runtime type references denote that descriptor in the match target. Arms are ordinary static expressions with a common result sort. `infer` binds type components. Matching is structural, with no implicit subtype matching or distribution over literal unions. Higher-rank callable binders are not arbitrarily decomposed. A named TypePatternRef may decompose only an observable known injective constructor layer/nominal argument structure. It MUST NOT infer inputs of an arbitrary type computation or a non-injective normalizing family such as Immut; `Constant<infer T>` and `Immut<infer T>` are not inverse patterns. Structural aliases may be expanded to supported observable layers without exposing alias identity.

An arm reduces only if it matches and all preceding arms are disjoint. A blocked target does not select the default. A full-Type-domain halt match MUST be exhaustive; a restricted domain must establish coverage at definition checking. Ordinary matches may report static failure, subject to Section 3 above.

```ril
halt type Head = \T: Type -> match type T {
    (infer H, ...infer Rest) -> H,
    _ -> type[never],
}
halt type Tail = \T: Type -> match type T {
    (infer H, ...infer Rest) -> Rest,
    _ -> type[()],
}
```

Tuple types/patterns reuse one tail `...`; tuple construction supports finite tuple spreads. String algorithms use ordinary string expressions and checked static library operations, not a separate template-string type language.

Types module builders are static closure interfaces. Functions with uncertain field uniqueness, callable scope, constructor constraints, literal category, or capacity return Result<Type,BuildError>. Callable descriptors preserve ordinary parameter write modes, generic/type-member binder scopes, effects, capabilities, and named origins. Implicit erasure applies to static binders, not parameter modes. No metadata operation converts an existing runtime value or silently removes its obligations.

`Types::require` is a closed declaration elaboration diagnostic: it extracts Ok(Type) or reports BuildError. It is not a halt callable and cannot be used in any halt declaration's elaboration or body. Its input must be closed, so a generic declaration cannot hide an unresolved success obligation. SafePlan interfaces below provide total generic alternatives.

## 6. Controlled Finite Graph Transformation

`Types::rewrite_graph` is a certified static primitive with callable sort:

```text
halt type(Type, halt type(Types::Layer) -> Result<Types::Fragment,Types::BuildError>)
    -> Result<Type,Types::BuildError>
```

It traverses a finite regular input graph once per input node. Layer exposes one known structure (array, Option, tuple, record, frozen modality, or a known atom). User nominal ADTs/wrappers, opaque representations, existential/dependent binders, and function signatures remain atoms. Unknown inputs remain neutral or blocked subtransforms; they are never silently classified as atoms.

Child edges have a region-scoped opaque Edge sort, not Type. They cannot be reflected, compared, numbered, converted to Type, independently returned, or stored in escaping closures. Synchronous nonescaping local callbacks may temporarily capture them. Edge -> Child construction is permitted only for output child positions.

Callbacks return finite Fragment objects containing guarded local constructors, completed atoms, and child edges. Newly generated output nodes are not added to the input workset. Provisional output Types are never exposed. Each edge ultimately points to the corresponding transformed input node. Final checks enforce kinds, source ownership, guarded recursion, frozen reachability, labels, nominal identity, and semantic capacities, returning BuildError normally.

Canonical field order is observable; alias names, defaults, graph-sharing implementation, and cache layout are not. Equivalent input graphs must produce equivalent results or the same error category. Internal graph counting/work storage MUST avoid hidden overflow; public descriptor-sequence capacity failures return CapacityExceeded.

`Types::SafePlan` is an opaque finite immutable plan built only by certified combinators: keep shape, optionalize source fields, remove field mut, select existing labels, and finite composition. It cannot contain arbitrary rewrite callbacks. Plans preserve unique labels, guarding, frozen modality, nominal/binder atoms, and legal constructors, so `Types::apply_graph(Type,SafePlan)` returns Type with no semantic builder-failure branch.

```ril
halt type DeepOptional = \T: Type ->
    Types::apply_graph(T, Types::optional_fields())
halt type DeepReadonly = \T: Type ->
    Types::apply_graph(T, Types::readonly_fields())
```

SafePlan composition is a finite constructor tree/DAG, evaluated in order using compiler-internal graphs, not oversized public arrays. Known outer constructors may be retained with neutral transformed children. DeepReadonly describes a different schema; it does not freeze a value or establish Shareable. Added wrappers under a frozen context must retain deep freezing.

Arbitrary path-sensitive rewriting, unbounded context growth, nonregular expansion, and fixed-point search are not supplied by this API. Ordinary type closures can express broader algorithms under resource budgets; they still cannot materialize an infinite literal union. AllPaths<Node> must use a depth bound or a recursive path representation when paths are infinite.

## 7. Explicit Operation Protocols

```ril
type Ordering { Less, Equal, Greater }
type Order<T> = { compare: fn(T, T) -> Ordering }
type CollectionAdapter<F<_>, G<_>> = { convert: fn<T>(F<T>) -> G<T> }
```

Protocols are ordinary runtime records containing operations, passed explicitly. Runtime function effects/capabilities retain their existing interface rules. There is no implicit implementation search or proof-assistant core: Eq, Refl, rewrite, Acc, user universes, and arbitrary runtime-dependent type computation are absent.


## 8. Boundary Acceptance Cases

```ril
type Ordinary = \T: Type -> type[int]
type Phantom<U> = int
-- Reject even if U is unused or the application was cached:
-- halt fn bypass(x: Phantom<Ordinary(type[int])>) -> int { x }

halt type PairWith = \U: Type, T: Type -> type[(T, U)]
type Pair = PairWith(type[str], type[int])
-- halt type PairWithHeader<U> = \T: Type -> type[(T,U)] -- reject
```

Equivalent provenance cases MUST cover imports, aliases, opaque public interfaces, typeof, defaults and graph rebuilding. Observing an ordinary runtime callable's already admissible signature via typeof is not invoking its body; any ordinary static computation needed to obtain that signature still violates the halt boundary.

SCC-inferred static closures must have resolved sorts before export. Recursive names are prebound items, while later lexical captures remain unavailable. Whole-tuple rest and a trailing comma after a rest are supported: `(...infer Rest)` and `(infer H, ...infer Rest,)`.

All static branching and local computation use ordinary expression/block grammar; type quotations contain data/sort syntax rather than a separate TypeIf/TypeBlock language. A computed alias can use a normal expression yielding Type; literal unit values remain different from quoted unit descriptions.
