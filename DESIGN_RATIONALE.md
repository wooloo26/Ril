# Ril Language Design Rationale

Design choices and their tradeoffs. [SPECIFICATION.md](SPECIFICATION.md) defines the authoritative rules; examples below use its independent-fixture convention. This document covers language semantics, not implementation design.

## Contents

- [Failure Model and Error Semantics](#failure-model-and-error-semantics)
  - [Defects and Recoverable Errors](#defects-and-recoverable-errors)
  - [Panics Are Not Algebraic Effects](#panics-are-not-algebraic-effects)
  - [No Synchronous Panic Catching](#no-synchronous-panic-catching)
  - [Assertive and Safe Partial Operations](#assertive-and-safe-partial-operations)
  - [Floating-Point and Collection Boundaries](#floating-point-and-collection-boundaries)
  - [Unit Success Without Implicit Wrapping](#unit-success-without-implicit-wrapping)
  - [Scoped Cleanup and Double Faults](#scoped-cleanup-and-double-faults)
- [Aliasing, Mutability, and the Law of Exclusivity](#aliasing-mutability-and-the-law-of-exclusivity)
  - [Rejecting Mutability Laundering](#rejecting-mutability-laundering)
  - [Call-Site Exclusivity Without Lifetime Annotations](#call-site-exclusivity-without-lifetime-annotations)
  - [Live Views Without a View Type Wrapper](#live-views-without-a-view-type-wrapper)
  - [Naming External Retained Sharing](#naming-external-retained-sharing)
  - [Transactional Derivation and Structural Sharing](#transactional-derivation-and-structural-sharing)
  - [Separating Reassignment and Interior Mutation](#separating-reassignment-and-interior-mutation)
  - [The Two Guarantees of clone_immut](#the-two-guarantees-of-clone_immut)
- [Algebraic Effects, Concurrency, and Function Colorlessness](#algebraic-effects-concurrency-and-function-colorlessness)
  - [Colorless Functions and Separated System Effects](#colorless-functions-and-separated-system-effects)
  - [Structured Scopes as Defect Boundaries](#structured-scopes-as-defect-boundaries)
  - [Capability-Based Concurrency Safety](#capability-based-concurrency-safety)
  - [Effect Confinement at Task Boundaries](#effect-confinement-at-task-boundaries)
  - [Persistent Handlers and Captured Environments](#persistent-handlers-and-captured-environments)
  - [Effect-Free Data Parallelism](#effect-free-data-parallelism)
  - [No Bare Atomics or Weak Memory Orderings](#no-bare-atomics-or-weak-memory-orderings)
  - [Channels and Endpoint Authority](#channels-and-endpoint-authority)
  - [Declarative Parallel Work Instead of Manual Slice Proofs](#declarative-parallel-work-instead-of-manual-slice-proofs)
  - [Leftmost Results and Deterministic Fault Visibility](#leftmost-results-and-deterministic-fault-visibility)
  - [Portable Collection Operations Instead of Core SIMD Types](#portable-collection-operations-instead-of-core-simd-types)
- [Syntax Ergonomics and Deliberate Omissions](#syntax-ergonomics-and-deliberate-omissions)
  - [Files as Modules and Predictable Namespaces](#files-as-modules-and-predictable-namespaces)
  - [Explicit Operation Records Instead of Implicit Instances](#explicit-operation-records-instead-of-implicit-instances)
  - [One Lexical Namespace](#one-lexical-namespace)
  - [Static Records and Dynamic Collections](#static-records-and-dynamic-collections)
  - [Nominal Wrappers and Single-Payload Packaging](#nominal-wrappers-and-single-payload-packaging)
  - [Opaque Types and Module Boundaries](#opaque-types-and-module-boundaries)
  - [Unit Nominal Domain Witnesses](#unit-nominal-domain-witnesses)
  - [Bindings Must Introduce Variables](#bindings-must-introduce-variables)
  - [Static Higher-Kinded Type Functions](#static-higher-kinded-type-functions)
  - [Constructor Tuples and Function Parameter Isolation](#constructor-tuples-and-function-parameter-isolation)
  - [Identifier Casing as Language Syntax](#identifier-casing-as-language-syntax)
  - [Flow Narrowing Without Rebinding](#flow-narrowing-without-rebinding)
  - [Two Where Tiers for Interfaces and Local Declarations](#two-where-tiers-for-interfaces-and-local-declarations)
  - [Projection Accessors for Product Types](#projection-accessors-for-product-types)
  - [Pure Type Functions Without a Second Schema Dialect](#pure-type-functions-without-a-second-schema-dialect)
  - [Generic Defaults and Const Values Instead of Literal Types](#generic-defaults-and-const-values-instead-of-literal-types)
  - [External Interfaces and the Sovereignty Axiom](#external-interfaces-and-the-sovereignty-axiom)
- [Tripartite Ontology and Asymmetric Scope of Influence](#tripartite-ontology-and-asymmetric-scope-of-influence)
  - [Three Domains: Shape, Access, and Control](#three-domains-shape-access-and-control)
  - [Callables Connect the Three Domains](#callables-connect-the-three-domains)
  - [Why Access Governs Bindings but Effects Govern Calls](#why-access-governs-bindings-but-effects-govern-calls)
  - [Domain Isolation Without Hidden Permission Changes](#domain-isolation-without-hidden-permission-changes)
  - [Independent Surviving Write Authorities](#independent-surviving-write-authorities)

## Failure Model and Error Semantics

### Defects and Recoverable Errors

```ril
let parsed: Result<int, str> = Err("invalid number")
let quotient = 10 / 0                  -- Panics: violated integer precondition
```

The original Midori-inspired distinction separates expected domain failures from broken program assumptions. `Result`/`Option` make recovery explicit; panic stops defective evaluation. A single exception category would let ordinary error handling accidentally conceal broken invariants.

### Panics Are Not Algebraic Effects

```ril
fn increment(n: int) -> int { n + 1 }  -- Can panic on overflow; no @Panic
```

Making every defect a checked effect would burden routine arithmetic and encourage blanket fault handlers. Ril keeps domain effects informative: handlers cannot intercept or resume a panic, and higher-order functions need no panic-specific variants.

### No Synchronous Panic Catching

```text
child panic -> scope failure -> Result<T, TaskFault>
parent panic -> child-exit barrier -> outward panic
```

A synchronous catch could continue with partially updated state. Supervision therefore belongs to a structured task boundary. Inspecting a child fault does not restore that scope to success; a parent's own panic is not converted into a catchable result by the same scope.

### Assertive and Safe Partial Operations

```ril
let item = items[index]                -- Precondition is asserted
let optional_item = items?[index]      -- Absence is a value
let quotient = numerator /? divisor
```

Known invariants should not require optional unwrapping at every use. Uncertain input should not require provoking a defect. Paired assertive and safe operations express these intentions with panic or a fallible value; range-checked conversions motivate the same distinction.

### Floating-Point and Collection Boundaries

```ril
let ratio = 1.0 / 0.0                  -- Positive infinity
let found = settings["theme"]         -- ?str
let window = items[start..end]
```

Floating arithmetic retains IEEE special values rather than treating every zero divisor as an integer defect. Missing map keys are routine domain conditions. For slicing, the original design favors clamping bounds and empty windows when the interval collapses, so window selection need not assert that one particular element exists. Precise accepted behavior is governed by the [collection rules](SPECIFICATION.md#range-and-slicing-expressions).

### Unit Success Without Implicit Wrapping

```ril
let saved: Result<(), str> = Ok()       -- Equivalent to Ok(())
let absent: ?int = None                -- A tag, not None()
let make_ok: fn(int) -> Result<int, str> = Ok
```

`Ok()` removes redundant unit parentheses while keeping success construction explicit. Implicit return wrapping would obscure nested results. Nullary tags remain values; unapplied payload constructors remain first-class functions. Construction and matching use the same distinction.

### Scoped Cleanup and Double Faults

```ril
let scoped mut resource = Resource.{
    name: "audit",
    on_close: \-> { events !> Array::push("closed") },
}
```

Cleanup needs state access, but cannot depend on unhandled effects or divergence while its context is leaving. Reverse registration order makes resource dependencies predictable. A second fault during panic, cancellation, or abort preserves both causes and stops that frame's remaining cleanup; it does not promise that every destructor succeeded. Pure parallel branches retain their separate fault-visibility contract.

## Aliasing, Mutability, and the Law of Exclusivity

### Rejecting Mutability Laundering

```ril
let item = Cell.{ count: 0 }
-- let mut alias = item                -- Error [E0520]
let mut copy = clone(item)
copy.count += 1
```

Permission survives wrapping, destructuring, insertion, and return; changing syntax must not bypass a read-only API. A deep clone creates separate storage, while a writable container never upgrades its elements. Iteration forbids structural changes through aliases. Unused authority and excessive concrete annotations are checked separately from interface capability bounds.

### Call-Site Exclusivity Without Lifetime Annotations

```ril
swap(mut cells[0], mut cells[1])        -- Requires disjoint reachable writes
-- swap(mut cells[0], mut cells[0])    -- Error [E0523]
```

The design places exclusivity obligations at calls rather than requiring user-written lifetime parameters. Different indices or names do not prove separation: independent arguments, ambient accesses, captures, and handlers all matter. Authorized use through the borrowed parameter is part of its loan; inactive aliases still permit sequential sharing.

### Live Views Without a View Type Wrapper

```ril
let view observed = working
let view read_title = \-> observed.title
let saved_title = observed.title
```

A view keeps the data shape T instead of turning every API into a T/View<T> pair. Binding permissions and origins retain its live nature. The observer follows changes to the pinned object; the copied string does not. A view initializer runs once, cannot supply mutable arguments, and cannot cross a task boundary as ordinary immutable data.

### Naming External Retained Sharing

```ril
fn publish(^mut entry: Entry) &^mut &{mut global_hub} {
    global_hub.entries !> Array::push(^mut entry)
}
```

`mut` permits temporary writes; `^mut` additionally permits retention. `&{^mut source}` names a source whose writable authority is published, not the container receiving it. Distinguishing source from destination prevents an intermediate local alias or helper call from concealing external sharing; purely local obligations can still be discharged.

### Transactional Derivation and Structural Sharing

```ril
let revised = base |> derive \mut draft -> {
    draft.child = external_immutable
    draft.child.count += 1
}
```

Confined mutation makes nested functional updates readable while immutable input/output permits unchanged sharing. Each source object, including newly inserted references, has one draft counterpart, preserving aliases and cycles without modifying the source. Abort publishes no result; it does not roll back unrelated external writes. Only unaffected regions may remain shared.

### Separating Reassignment and Interior Mutation

| Binding | Slot | Referenced ordinary data |
| :--- | :--- | :--- |
| `let` | Fixed | Immutable; sharing allowed |
| `let mut` | Pinned | Writable with granted permissions |
| `var` | Reassignable | Keeps the value's permissions |
| `let view` | Fixed observation | Read-only, possibly changing |

Separating slot replacement from interior writes expresses stable mutable handles directly. Scalars use `var`; `mut` parameters cannot misleadingly rebind the caller's handle. Read-only access alone does not establish the stronger ordinary `let` guarantee.

```ril
fn make_numbers() -> []int {
    let mut values: []int = []
    values !> Array::push(1)
    values
}
let numbers = make_numbers()
```

Construction-only writers end at return. With no surviving outside writer or active environment, the caller can receive immutable data without a second deep copy.

### The Two Guarantees of clone_immut

```ril
let mut independent = clone(observed)
let snapshot = clone_immut(observed)
independent.count += 1
```

`clone_immut` combines isolation from the source with immutable result data. Merely removing a view's write permission would not provide either guarantee. Eligibility covers the whole ordinary graph: views and wrappers cannot hide a non-copyable environment or resource. Internal aliases remain internal aliases; `Immut<T>` records immutability without implying uniqueness.

## Algebraic Effects, Concurrency, and Function Colorlessness

### Colorless Functions and Separated System Effects

```ril
eff Yield<T> { emit(T) -> () }
type Fetch = fn(str) -> Result<str, str> @Fiber
-- @Async = {Fiber, Concurrent}
```

Suspension changes a computation's obligations, not its ordinary return shape or call syntax. Higher-order functions can forward those obligations without separate async combinators. Leaf I/O uses Fiber; task creation requires Concurrent. Typed Yield data is distinct from unit-valued Fiber scheduling, so a stream consumer cannot accidentally intercept scheduler operations. Affine resume supports push streams; pull state must be represented explicitly.

### Structured Scopes as Defect Boundaries

```text
Task<T>.join()           -> Result<T, TaskFault>
Task<Result<T, E>>.join() -> Result<Result<T, E>, TaskFault>
```

Children cannot outlive their scope, so results and cleanup have an explicit rendezvous. Failure cancels descendant and body waits, blocks new forks, and remains failure after inspection. The exit barrier is a lifetime guarantee, not a promise to terminate arbitrary divergence. A business Result retains its own inspection obligation instead of disappearing inside Task.

### Capability-Based Concurrency Safety

```ril
let snapshot = clone_immut(observed)
let task = s.fork(\-> snapshot.count)
-- Capturing observed itself across this boundary is E0601.
```

Task safety follows actual permissions, origins, and immutable data rather than a separate set of nominal marker traits. A simple visible type cannot hide live state in a closure or aggregate. Resource transfer and confined parallel writes have explicit contracts rather than weakening the general boundary rule.

### Effect Confinement at Task Boundaries

```ril
let task = s.fork(\-> {
    with WorkerLog::log(_message) -> resume ()
    WorkerLog::log("started")
    42
})
```

A child must not resume or abort an ancestor's active computation. It installs local handlers, possibly using passed immutable handler data. Memory confinement and control confinement therefore reinforce each other; join and channels carry results between tasks instead of cross-task continuations.

### Persistent Handlers and Captured Environments

```ril
type Button = { on_click: fn() -> () }
fn button_for(label: str) -> Button &capture {
    Button.{ on_click: \-> {
        with Console::print(_message) -> resume ()
        Console::print(label)
    } }
}
```

Escape is safe when each invocation has stable handling. Retaining a handler retains its definition and lawful environment, never an old continuation or return target. Every final arm value, including a tail after resume, must fit the new answer type. Creating a surviving environment still requires capture authority, even inside a returned record; handling its effects does not remove that duty.

### Effect-Free Data Parallelism

```ril
halt fn squares(values: []f64) -> []f64 {
    values |> Parallel::map(\x -> x * x)
}
```

Independent evaluation does not require a new control-request effect named Parallel. The callback's residual effects, including Div, must be empty, though local handling and immutable captures remain useful. A fixed 64-element reduction tree supplies its own reference semantics; it is not ordinary left-fold equivalence or a claim that floating addition is associative.

### No Bare Atomics or Weak Memory Orderings

```text
shared reading      -> immutable data
task coordination   -> structured channels
parallel mutation   -> explicit disjoint regions
```

An ordinary immutable handle must not conceal an operation that changes its reachable data. Bare atomics and memory-order flags would add another shared-state model beside these permissions. Ril keeps communication under explicit resource/effect contracts rather than adding an interior-mutation exception to `let`.

### Channels and Endpoint Authority

```ril
-- Inside a child task; tx is an immutable sender descriptor.
let mut local_tx = clone(tx)
(local_tx !> Channel::send(message))
    ?? \_error -> panic("receiver closed")
Channel::close(local_tx)
```

Sender clones keep channel identity but gain independent endpoint authority, so this resource operation has Fiber rather than an ordinary deep-copy guarantee. Protocol state is effect-accessed external state, not a mutable child of an immutable descriptor. Detach/attach explicitly transfer unique authority; close and scope/task exit determine lifetime without depending on garbage collection.

### Declarative Parallel Work Instead of Manual Slice Proofs

```ril
cells !> Parallel::for_each(\mut cell -> { cell.count *= 2 })
let (left, right) = Parallel::join(\-> sort(left_part), \-> sort(right_part))
```

Element operations and divide-and-conquer describe the intended work without introducing low-level slice-borrow syntax. They still require actual disjoint access; different paths into shared objects do not suffice. Mutable join/for_each finish independent work and retain writes before reporting faults, rather than implying rollback or sequential short-circuit state.

### Leftmost Results and Deterministic Fault Visibility

```ril
let found = [0, 1] |> Parallel::find(\x -> {
    if x == 0 { true } else { panic("right branch") }
})
assert(found == Some(0))
```

Pure reference evaluation, not arrival order, chooses the observable match or fault. A skipped rightward branch cannot preempt an earlier answer, even with a branch-local double fault. Branch state and cleanup obligations must therefore remain local; a selected double fault still keeps its fatal severity. Structured concurrency does not inherit this pure determinism promise.

### Portable Collection Operations Instead of Core SIMD Types

```ril
let squares = values |> Array::map(\x -> x * x)
```

Core application types describe domain data, not hardware lane widths and masks. Ordinary collection operations keep that meaning portable; specialized numeric operations can live in libraries. This retains the original choice against core SIMD syntax without prescribing how an implementation evaluates the operation.

## Syntax Ergonomics and Deliberate Omissions

### Files as Modules and Predictable Namespaces

```ril
use math/geometry                     -- Geometry namespace
use ril/crypto as Hash
let words = "a,b" |> String::split(",")
```

A file already supplies a module boundary, so another wrapper adds little information. `pub` exposes its interface; local imports keep dependencies near use. Lowercase paths map to predictable PascalCase namespaces. Array/Map/Set/String are common enough for the prelude; specialized type extractors remain module exports.

### Explicit Operation Records Instead of Implicit Instances

```ril
type Ordering<T> = { less: fn(T, T) -> bool }
fn before<T>(ops: Ordering<T>, left: T, right: T) -> bool {
    ops.less(left, right)
}
```

Passing operations explicitly makes the selected behavior visible and permits multiple choices for the same data type. It avoids implicit-instance coherence and orphan-rule questions, and does not turn built-in operators into hidden user calls. Actual callback effects and permissions still follow the supplied operations.

### One Lexical Namespace

```ril
use math/geometry                     -- Binds Geometry
-- type Geometry = int                -- Error [E0203]: same-scope name already exists
```

A name should identify one declaration without a second type/value import dialect. Nominal type and constructor uses are roles of the same declaration, not unrelated duplicate entities. This keeps references, imports, and renaming consistent; casing supplies additional grammatical role information.

### Static Records and Dynamic Collections

```ril
type User = { id: int, name: str }
type Id = User.id
let settings: [str: str] = ["theme": "dark"]
let theme = settings["theme"]          -- ?str
use ril/array::{Elem}
type Item = Elem<[]int>
```

Records have known fields; maps and arrays have collection operations. `r.field` and a static `r.(key)` preserve this distinction, while run-time record keys remain invalid. Named rows preserve extra fields and `..rest` binds a typed remainder. Product projection uses dots; collection parameter extraction uses explicit helpers or type matching. Sets use ordinary `Set` constructors, not extra core literal syntax.

### Nominal Wrappers and Single-Payload Packaging

```ril
type UserId(int)
type OrderId(int)
type Point({ x: f64, y: f64 })
let user_id = UserId(42)
let raw = inner(user_id)
```

Equal representations need not denote interchangeable domains. Wrappers distinguish identifiers and coincidentally equal record shapes while retaining their underlying value/reference behavior. One payload can be a scalar, record, or tuple, avoiding a separate packaging model for every shape.

### Opaque Types and Module Boundaries

```ril
pub opaque type Token = str
pub fn reveal(token: Token) -> str { token } -- Inside the defining module
```

Opaque types allow direct representation use inside their module while preserving validation boundaries outside it. Public functions and pipelines expose deliberate operations; external `inner` or pattern penetration would bypass that choice (`E0308`). The distinction is module authority, not an additional application-visible wrapper payload.

### Unit Nominal Domain Witnesses

```ril
type Marker
let marker: Marker = Marker
let result: Result<Marker, str> = Ok(Marker)
```

A zero-payload domain identity remains useful even without stored data. Marker is distinct from unit, so `Ok()` cannot silently replace `Ok(Marker)`. Visibility and opacity control who can create protected witnesses; a publicly constructible marker is simply a nominal value.

### Bindings Must Introduce Variables

```ril
let UserId(id) = user_id
-- let Marker = marker                -- Error [E0309]: no variable introduced
let _ = marker                        -- Explicit discard
```

`let` should introduce a usable name, not disguise an assertion or branch. Non-vacuous patterns make this expectation consistent across ordinary and guarded bindings. Use `is`, `match`, or `?` when no binding is needed; `_` does not waive a Result's inspection obligation.

### Static Higher-Kinded Type Functions

```ril
type Wrap = \M: Type -> Type, T -> type<M<T>>
type OptionalInt = Wrap<Option, int>
```

Higher-kinded parameters support reusable shape transformations without introducing run-time type construction or type unification. Kinds and call families stay static; ordinary operation records provide value-level behavior. This preserves the original phase distinction without tying it to a representation strategy.

### Constructor Tuples and Function Parameter Isolation

```ril
let reply: Result<(int, str), str> = Ok(200, "ready")
-- Ok((200, "ready")) constructs the same payload.
fn add(left: int, right: int) -> int { left + right }
-- add((1, 2))                         -- Error [E0314]
```

Constructor tuple equivalence removes redundant parentheses without merging ordinary function parameters, defaults, or modes. It applies once at the outer payload boundary, never recursively flattens nested tuples, and cannot deconstruct an unconstrained T as a tuple. Unit, scalar/whole-tuple, and multi-field cases remain distinct; one-element tuples are absent.

### Identifier Casing as Language Syntax

```ril
type HttpServer = { port: int }
meta let DEFAULT_PORT = 8080
var active_connections = 0
```

Casing makes constructor tests, variable bindings, types, and constants distinguishable at their use sites. All-caps belongs to static/top-level immutable constants, not mutable state; acronyms use title casing and module paths use snake_case. Static-key binders and generated schema labels retain the specification's explicit exceptions rather than weakening ordinary variable rules.

### Flow Narrowing Without Rebinding

```ril
fn display_name(user: ?User) -> str {
    if user != None { user.name } else { "Anonymous" }
}
```

`match` decomposes alternatives, guarded let extracts a name or exits, and narrowing refines an existing name. Immutable data supports stable facts; reassignment and overlapping writes invalidate live ones. Three projections and three loop-refinement rounds bound the specified precision, without promising analysis timing or treating a view as immutable data.

### Two Where Tiers for Interfaces and Local Declarations

```ril
fn run(value: int, action: Action) -> int
where
    type Action = fn(int) -> int
{
    adjust(action(value))
where
    fn adjust(n: int) -> int { n + 1 }
}
```

Signature where keeps interface aliases beside the contract; block where keeps helpers, private types, and locally discharged effects beside the body. Downward references and duplicate tier names would make the public contract depend on hidden declarations. Separating declarations from sequential bindings also makes hoisting and evaluation order explicit.

### Projection Accessors for Product Types

```ril
let names = users |> Array::map(\.name)
let ids = pairs |> Array::map(\.0)
let leaders = departments |> Array::map(\.leader?.name)
```

Field and tuple projections need no repeated lambda parameter names. Safe navigation preserves optional access. Collections keep explicit indexing/combinators because an element may be absent; pretending that an array has a `.0` product field would hide that different contract.

### Pure Type Functions Without a Second Schema Dialect

```ril
type Handlers = \T, R -> type<{ [K in keyof T]: fn(T.(K)) -> R }>
halt type Element = \T -> match type<T> {
    type<[]let E> -> type<E>,
    _ -> type<never>,
}
```

- Ordinary if/match and pure collection operations express schema transformations; a separate macro or remapping dialect is unnecessary.
- Type functions synthesize shapes. Meta functions compute values and inspect known type tokens without gaining type-return authority.
- `keyof` and projection share a coordinate model: sorted names for records/sums, ordered indices for tuples. A nullary tag's payload domain is unit, not never; equal types therefore expose equal coordinates.
- Explicit `let U` type binders, linear patterns, and known constructor heads keep matching unambiguous. Static branch pruning prevents unreachable branches from imposing effect obligations.

```ril
fn get_field<T, K: keyof T>(record: T, key: K) -> T.(K) { record.(key) }
```

The static-key form preserves common field-access syntax while requiring a known member of T. It does not promote arbitrary run-time strings into types.

### Generic Defaults and Const Values Instead of Literal Types

```ril
type Matrix<T, rows: int, cols: int = rows> = { data: []T }
type HttpMethod { Get, Post }
type Quantity<m: int, l: int, t: int>(f64)
```

Data-type defaults reduce repeated arguments; callable generics instead use inference or explicit arguments. Defaults follow trailing and left-to-right dependency rules. Constants can parameterize shapes, dimensions, units, or route schemas without becoming bare literal types; tagged sums represent discrete domain states. Equal static argument values have the same type meaning, but a length parameter alone promises no inline layout.

### External Interfaces and the Sovereignty Axiom

```ril
-- platform/dom.d.ril
pub type DomElement
pub fn set_text(mut element: DomElement, text: str) -> () @Fiber &mut
```

The Ril contract remains the source of typing, effect, permission, and failure guarantees at an external boundary. Declaration units reuse ordinary syntax instead of adding foreign-only keywords or untyped escape types. Opaque handles prevent structural penetration; host failures must respect typed domain-error or supervised-panic contracts rather than leak a second error model.

## Tripartite Ontology and Asymmetric Scope of Influence

### Three Domains: Shape, Access, and Control

```ril
type Buffer = { mut bytes: []u8 }       -- Shape and field declaration
let mut buffer = Buffer.{ bytes: [] }  -- Binding authority
buffer.bytes !> Array::push(0)
```

| Domain | Question |
| :--- | :--- |
| Shape | What values and fields exist? |
| Access | Which storage may this use read, write, retain, or rebind? |
| Control | Which operations may transfer control to a handler? |

Separating the questions prevents a field's mut marker from becoming an ambient capability or an effect annotation from becoming a property of passive data.

### Callables Connect the Three Domains

```ril
type Reader = fn(mut []u8) -> int @Fiber &mut
type Action = fn() -> ()               -- Inferred obligations remain attached
type ClosedAction = fn() -> () @{} &{}
```

A callable combines input/output shapes, access obligations, and control effects, and can itself be stored as data. Simplified types should not expose every captured variable, but must preserve its obligations. Concrete definitions declare direct state access; callback forwarding never changes parameter modes. Explicit empty rows express a closed contract rather than relying on omission.

### Why Access Governs Bindings but Effects Govern Calls

```ril
fn read_line() -> str @Console {
    let value = Console::read_line()
    value
}
```

The returned string does not need an effect-colored data type: its producing operation has already occurred. Binding permissions still matter because references can remain shared. A stored callable is different from an already evaluated passive result: its future invocation retains effects and state obligations. Immutable callable data therefore does not imply pure computation.

### Domain Isolation Without Hidden Permission Changes

```ril
type Service = { fetch: fn() -> str @Io }
-- type EffectAsData = @Io             -- Error [E0330]
-- type PermissionAsData = &mut        -- Error [E0331]
-- type Invalid = { value: str @Io }   -- Error [E0333]
```

| Boundary | Diagnostic |
| :--- | :--- |
| Bare effect/capability aliases | E0330 / E0331 |
| Computation annotations on variant tags or passive fields | E0332 / E0333 |
| Effect/capability constraints on data type parameters | E0334 |
| Effect/capability annotations on type computations | E0335 |
| Effects on passive value bindings | E0613 |
| Meta type return / meta computation annotations | E0812 / E0813 |

These restrictions preserve the distinction between storing a callable and storing its permissions as ordinary data. Type-level abstraction must not erase an actual sharing hazard or create a write permission.

### Independent Surviving Write Authorities

```text
private cell -> one escaped mutable closure       : &capture
same cell -> closure plus direct reference        : &capture and &^mut
borrowed cell -> retained external reference      : &^mut
```

This preserves the original surviving-write-path idea while counting independent authorities rather than repeated graph walks. Cycles or two fields in one fresh passive graph do not alone create extra external owners. Named sources remain identifiable through aliases, and local discharge cannot hide an origin that still has an outside writer.
