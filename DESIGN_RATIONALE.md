# Ril Language Design Rationale

Design choices, tradeoffs, and reference languages. Examples are independent fixtures: local statements run in an enclosing callable, free names are typed inputs, and required local handlers are supplied. Named functions obey their written annotations.

## Contents

- [Standard Library Boundaries and Local Tooling](#standard-library-boundaries-and-local-tooling)
- [Failure Model and Error Semantics](#failure-model-and-error-semantics)
  - [Defects and Recoverable Errors](#defects-and-recoverable-errors)
  - [Panics Are Not Algebraic Effects](#panics-are-not-algebraic-effects)
  - [No Synchronous Panic Catching](#no-synchronous-panic-catching)
  - [Assertive and Safe Partial Operations](#assertive-and-safe-partial-operations)
  - [Floating-Point and Collection Boundaries](#floating-point-and-collection-boundaries)
  - [Unit Success Without Implicit Wrapping](#unit-success-without-implicit-wrapping)
  - [Scoped Cleanup and Double Faults](#scoped-cleanup-and-double-faults)
- [Diagnostics and Failure Classification](#diagnostics-and-failure-classification)
  - [Conditions Before Message Wording](#conditions-before-message-wording)
  - [Advisory Warnings and Mandatory Errors](#advisory-warnings-and-mandatory-errors)
  - [Failure Categories Without New Runtime Types](#failure-categories-without-new-runtime-types)
- [Aliasing, Mutability, and the Law of Exclusivity](#aliasing-mutability-and-the-law-of-exclusivity)
  - [Rejecting Mutability Laundering](#rejecting-mutability-laundering)
  - [Complete Provenance Without Repeating It in Source](#complete-provenance-without-repeating-it-in-source)
  - [Default Purity and Declared Concrete Obligations](#default-purity-and-declared-concrete-obligations)
  - [Source Groups and Public Function Contracts](#source-groups-and-public-function-contracts)
  - [Call-Site Exclusivity Without Lifetime Annotations](#call-site-exclusivity-without-lifetime-annotations)
  - [Live Views Without a View Type Wrapper](#live-views-without-a-view-type-wrapper)
  - [Naming External Retained Sharing](#naming-external-retained-sharing)
  - [Transactional Derivation and Structural Sharing](#transactional-derivation-and-structural-sharing)
  - [Separating Reassignment and Interior Mutation](#separating-reassignment-and-interior-mutation)
  - [The Two Guarantees of clone_immut](#the-two-guarantees-of-clone_immut)
- [Algebraic Effects, Concurrency, and Function Colorlessness](#algebraic-effects-concurrency-and-function-colorlessness)
  - [Colorless Functions and Separated System Effects](#colorless-functions-and-separated-system-effects)
  - [Termination Facts and Finite Evaluation](#termination-facts-and-finite-evaluation)
  - [Parameterized Handlers and Budget Configuration](#parameterized-handlers-and-budget-configuration)
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

## Standard Library Boundaries and Local Tooling

```ril
let words = "a,b" |> String::split(",")
use ril/file
use ril/path
use ril/io
fn load(path: Path::Path) -> Result<str, str> @Fiber {
    Results::map_err(File::read_text(path), Io::error_text)
}
```

The closed prelude makes common values and collection namespaces immediately available. `Options` and `Results` name the transformation modules; `Option<T>` and `Result<T, E>` keep their type roles. Prelude aliases avoid repeated `use ... as ...` declarations without changing the normal module-name derivation rule. Rust's [prelude documentation](https://doc.rust-lang.org/std/prelude/index.html) provides a reference for an explicit automatic-import surface.

The library's local-tooling baseline covers text, collections, numeric conversion, binary encoding, filesystem access, native paths, environment data, child processes, and testing. Go's [standard library index](https://pkg.go.dev/std) and [binary encoding package](https://pkg.go.dev/encoding/binary) are references for this breadth and for specifying portable data encodings independently of machine layout. These general operations support self-hosted local tools without prescribing their internal design. Network protocols and general serialization remain separate future scope.

```ril
use ril/os
use ril/path
let native_path = Path::from_native(native_name)
let display = Path::to_string(native_path)
match display { Ok(text) -> println(text), Err(_error) -> println("non-Unicode path") }
```

Native names cannot always be represented by a Unicode string. Rust's [OsString documentation](https://doc.rust-lang.org/std/ffi/struct.OsString.html) describes this distinction for Unix bytes and Windows UTF-16. Ril therefore preserves native data and makes Unicode conversion fallible. Lexical normalization is separate from filesystem canonicalization because links can change what a path traversal means. The [Unicode 17.0.0 reference](https://www.unicode.org/versions/Unicode17.0.0/) fixes text classification and case conversion for this library version; it does not alter Ril's identifier syntax or scalar-counting convention.

Go's [I/O contracts](https://pkg.go.dev/io) demonstrate why progress and an error can coexist. Ril's stream operations expose committed prefixes and require helpers to retry only unwritten bytes. Implicit file release has a narrowly specified finite contract; error-reporting close, flush, and process cleanup remain explicit operations or effectful wrappers. This keeps the language's scoped-cleanup restrictions intact. Process arguments follow an explicit vector model, with the Windows interpretation boundary recorded in the contract; Rust's [Command documentation](https://doc.rust-lang.org/std/process/struct.Command.html) provides a corresponding reference for separating arguments from shell parsing.

Deterministic collections, seeded random sequences, and binary byte order support reproducible ordinary computations. Stable content digests use [FIPS 180-4 SHA-256](https://csrc.nist.gov/pubs/fips/180-4/upd1/final); internal collection hashing is not a persistence format. Environmental observations still declare their effects and do not become deterministic merely because the surrounding algorithm is pure.

Cloning affects provenance, derive confines draft authority, and Div bounds covered computation. Their rules concern general language semantics. Channel protocols, parallel reference evaluations, and test conventions describe concrete APIs. This distinction keeps syntax and general semantics separate from the library surface.

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
let items = [10, 20]
let window = items[0..1]
let empty = items[len(items)..len(items)] -- Valid empty half-open window
-- items[2..1]                        -- Panics: reversed bounds
-- items[0..3]                        -- Panics: upper bound exceeds the length
```

Floating arithmetic retains IEEE special values. Missing map keys are ordinary absence. Half-open slices permit an empty window at the end; negative, reversed, or out-of-range bounds panic instead of being clamped.

### Unit Success Without Implicit Wrapping

```ril
let saved: Result<(), str> = Ok()       -- Equivalent to Ok(())
assert(saved is Ok())
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

LIFO cleanup preserves resource order; calling the current `on_close` gives replacement its ordinary meaning without a destructor protocol or snapshot. Double faults preserve both causes rather than promise successful cleanup. Channel closing and parallel fault visibility keep their separate contracts.

## Diagnostics and Failure Classification

### Conditions Before Message Wording

```ril
type User = { id: int, name: str }
let user = User.{ id: 1, name: "Ada" }
-- let missing: User = .{ id: 1 }     -- Error [E0307]: construction lacks a required field
-- let unknown = user.age            -- Error [E0336]: projection names no declared field
```

These failures need different corrections even though both involve record fields. Dedicated conditions similarly separate ambiguous constructors from duplicate declarations, uninitialized captures from unavailable names, and refutable bindings from nonexhaustive matches. General type mismatch remains useful when no narrower language rule applies.

Fixed rejection conditions and diagnostic identities permit flexible message wording and presentation. A useful explanation names the failed requirement and connects it to the responsible declaration, expected type, or authority source. Suggested changes must respect the distinction between explaining a rule and choosing the program's intended behavior; adding sharing or an effect obligation can change the contract.

The [C# statements specification](https://learn.microsoft.com/en-us/dotnet/csharp/language-reference/language-specification/statements#132-end-points-and-reachability) states diagnostic conditions beside the relevant rules and examples. The [Rust Reference's diagnostic attributes](https://doc.rust-lang.org/reference/attributes/diagnostics.html) distinguish diagnostic levels and separate the supported lint catalog from the reference's language-level rules. Ril follows that separation of concerns while retaining its existing normative error-code convention.

### Advisory Warnings and Mandatory Errors

```ril
let unused = 1                       -- Warning [W0001]: valid unused read-only binding
let _intentional = 1                 -- OK
-- let mut unused_items: []int = []  -- Error [E0527]: mutable authority must be exercised
-- let _ = parse_id("42")            -- Error [E0720]: discard does not inspect a Result
```

An unused read-only binding, unused private import, or unreachable sequential statement can be reported without making the program invalid. Warning coverage is advisory rather than a promise to discover every useless computation. Implicit scoped cleanup and public re-exports count according to their actual contracts, not merely whether an ordinary expression mentions a name.

Mutable-authority use, Result inspection, and match-arm reachability already participate in Ril's mandatory rules. Reclassifying them as optional warnings would weaken those rules. The underscore convention suppresses only intentionally unused read-only names; it cannot waive authority or fallible-result obligations.

### Failure Categories Without New Runtime Types

```ril
-- let quotient = 1 / 0              -- Panics: ordinary integer division
-- meta let QUOTIENT = 1 / 0         -- Error [E0831]: failure in required static evaluation
let quotient = 1 /? 0                -- OK: None
```

The distinction is the evaluation domain and operation contract, not whether a defect happens to be predictable. Turning a predictable ordinary panic into rejection would change the language's existing execution rules. Safe operations and business Result values remain explicit alternatives with their own semantics.

The [Go specification's run-time panic section](https://go.dev/ref/spec#Run_time_panics) defines execution conditions without fixing distinct error values for every condition. Ril likewise documents the triggers without adding a category field to `PanicInfo` or changing `TaskFault`. Cancellation, effect abort, and double faults keep their separate propagation and cleanup rules. Examples check the specified outcome rather than an explanatory message's exact wording.

## Aliasing, Mutability, and the Law of Exclusivity

### Rejecting Mutability Laundering

```ril
let item = Cell.{ count: 0 }
-- let mut alias = item                -- Error [E0520]
let mut copy = clone(item)
copy.count += 1
```

Permission survives wrapping, destructuring, insertion, and return; changing syntax must not bypass a read-only API. A deep clone creates separate storage, while a writable container never upgrades its elements. Iteration forbids structural changes through aliases. Unused authority and excessive concrete annotations are checked separately from interface capability bounds.

### Complete Provenance Without Repeating It in Source

```ril
fn identity(cell: Cell) -> Cell { cell }
let immutable = Cell.{ count: 0 }
-- let mut stolen = identity(immutable) -- Error [E0528]: return preserves the immutable origin

fn invoke(action: fn() -> ()) { action() }
-- Callback effects, state access, and captured origins remain attached.

var count = 0
fn advance() &{mut count} { count += 1 }
fn invoke_pure(action: fn() -> ()) @{} &{} { action() }
fn check_choice(choose_write: bool) {
    let action = if choose_write { advance } else { \-> () }
    -- invoke_pure(action)
    -- Error [E0534]: a run-time alternative retains the possible external write
}
```

Ordinary return types, compact callable types, and ordinary calls keep business code readable. They do not discard information: the machine retains the possible origins, permissions, immutable or live status, captured environments, existing sharing relations, and residual effects of each value. A simplified type is an abstraction of these facts, not evidence that they are absent. Unknown overlap is not a developer promise of disjointness.

Complete inference preserves relevant facts and covers the specified conservative judgments. It does not promise exact prediction of arbitrary run-time behavior. Unknown facts cannot establish independence, purity, or absence of escape; the possible write in `check_choice` remains an obligation.

Complete provenance is a machine obligation. The corresponding diagnostic can expand the relevant inferred facts and their causal chain: the original binding, aliases or aggregate paths, calls and returns, captured environments or handlers, and the conflicting use. This gives a programmer the reason for a rejection without requiring every intermediate fact in source or asking the programmer to verify its safety. Those explanations do not define another annotation language or weaken source-level checks.

Machine-supplied annotations record a valid inferred contract. They cannot repair a semantic conflict by widening permission, silently inserting a clone, or changing an alias into independent data. Missing declarations and incompatible intentions therefore remain distinguishable: routine annotation work can be supplied mechanically, while correcting an invalid ownership or sharing choice requires a visible program change.

### Default Purity and Declared Concrete Obligations

```ril
var count = 0
fn advance() &{mut count} { count += 1 }
fn invoke(action: fn() -> ()) { action() }
fn declared() &{mut count} { invoke(advance) }
-- fn hidden() { invoke(advance) }    -- Error [E0510]
fn invoke_pure(action: fn() -> ()) @{} &{} { action() }
-- invoke_pure(advance)               -- Error [E0534]
fn plain() {}
-- fn noisy() @{} &{} {}             -- Error [E0542]
-- type ClosedAction = fn() -> () @{} &{} -- Error [E0542]
```

Default purity gives an ordinary named definition a useful meaning without extra syntax: it has no undeclared concrete outward state or residual effects. Calling another function does not make a known dependency disappear. Callback parameters are different: their actual obligations depend on the value supplied, so the language preserves that dependency until use rather than forcing repeated forwarding notation. The ordinary caller that supplies `advance` has a concrete obligation again.

Empty rows express callback constraints at higher-order boundaries. Ordinary definitions use default purity, while first-order callable types retain inferred obligations. This places each constraint at the call that needs it.

### Source Groups and Public Function Contracts

```ril
type Step = fn() -> int &closure
fn make_step(increment: int) -> Step &capture {
    var count = 0
    step
    where
        fn step() -> int &{closure, increment, mut count} {
            count += increment
            count
        }
}
```

The group records one capture layer while retaining each binding's mode. A farther named layer can be named explicitly; anonymous layers need no invented source names. Grouping cannot identify objects or prove independence: two declarations named `count`, two invocations of one factory, and two paths to one object remain different questions. Ordinary blocks do not add another function layer, but their bindings and lifetimes are not merged. Global groups, captured groups, and the independent creation and retention annotations keep those distinctions visible.

```ril
-- counter.ril
var private_count = 0
pub fn advance() &{mut private_count} { private_count += 1 }

-- client.ril
use counter
fn wrapper() &Counter::advance { Counter::advance() }
```

Requiring a caller to declare known state must not require it to name private storage in another module. The public function already has a checked contract, so its named state can be referenced on a named wrapper without another declaration kind. This reference covers inherited named obligations, not direct access in the wrapper. It imports neither effects nor independent parameter, environment-creation, or retention obligations. Restricting this form to named definitions keeps callable-type budgets and anonymous inference unchanged.

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

```ril
var count = 0
fn read_count() -> int &{count} { count }
count += 1
assert(read_count() == 1)
```

A bare item in either source-group kind means read-only access, whether the source is immutable or live. It does not create a view binding or establish deep immutability. Global `&{name}` and captured `&{closure, name}` distinguish lexical sources while using the same read mode; actual source facts still determine view eligibility, refinement stability, and task confinement.

### Naming External Retained Sharing

```ril
fn publish(^mut entry: Entry) &^mut &{mut global_hub} {
    global_hub.entries !> Array::push(^mut entry)
}
```

`mut` permits temporary writes; `^mut` additionally permits retention. `&{^mut source}` names a source whose writable authority is published, not the container receiving it. Distinguishing source from destination prevents an intermediate local alias or helper call from concealing external sharing; purely local obligations can still be discharged.

```ril
let mut source = Cell.{ count: 0 }
-- let mut hidden = source            -- Error [E0510]: local writable alias needs ^mut
let mut alias = ^mut source
alias.count += 1
let mut pair = (^mut source, ^mut source)
pair.0.count += 1
assert(source.count == 2 && pair.1.count == 2)
```

Local discharge concerns a function's outward contract; it does not hide a second local writable authority. `^mut` marks an alias, store, or destructuring of an existing writable value, including an aggregate member, while preserving the source's permissions and identity. It cannot grant a view write access. Lexical capture and ordinary returns retain their inferred provenance and existing capability checks. Later writes through an existing shared authority do not create another publication merely because sharing already exists.

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
| `var` | Reassignable | Read-only access; no interior writes through this binding |
| `var mut` | Reassignable | Writable only with granted origin permissions |
| `let view` | Fixed observation | Read-only, possibly changing |

```ril
var selected = Cell.{ count: 0 }
selected = Cell.{ count: 1 }
-- selected.count += 1                -- Error [E0520]: reassignable slot is not interior write authority

var mut working = Cell.{ count: 0 }
working.count += 1
working = Cell.{ count: 2 }
```

Separating slot replacement from interior writes expresses stable mutable handles directly. Scalars use `var`; replaceable writable handles use `var mut`. Both of a `var mut` binding's authorities must be exercised: slot reassignment and its granted interior/environment write authority. A binding that only needs the latter uses `let mut`; unused authority is rejected under `E0527`. Neither spelling upgrades an immutable or live read-only origin. Mutable parameters remain pinned and cannot misleadingly rebind the caller's handle. Read-only access alone does not establish the stronger ordinary `let` guarantee.

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

Ascription records the existing immutable guarantee without hidden copying, freezing, or restored write permission.

## Algebraic Effects, Concurrency, and Function Colorlessness

### Colorless Functions and Separated System Effects

```ril
eff Yield<T> { emit(T) -> () }
type Fetch = fn(str) -> Result<str, str> @Fiber
-- @Async = {Fiber, Concurrent}
```

Suspension changes a computation's obligations, not its ordinary return shape or call syntax. Higher-order functions can forward those obligations without separate async combinators. Leaf I/O uses Fiber; task creation requires Concurrent. Typed Yield data is distinct from unit-valued Fiber scheduling, so a stream consumer cannot accidentally intercept scheduler operations. Affine resume supports push streams; pull state must be represented explicitly.

Termination is an inferred callable property separate from effect rows. `Div` names the budget-exhaustion request; it does not label every potentially infinite computation. An empty effect row describes absence of residual requests, not a proof that computation ends.

### Termination Facts and Finite Evaluation

```ril
fn spin() -> int { loop {} }
fn countdown(n: int) -> int {
    if n <= 0 { 0 } else { countdown(n - 1) }
}
halt fn checked(n: int) -> int { countdown(n) }

halt fn bounded() -> ?int {
    with Div::exhausted() -> None
    with Div::budget(10_000)
    Some(spin())
}
```

Ordinary functions receive the same termination judgments as `halt` functions. The annotation makes outward purity and finite computation mandatory instead of enabling a more favorable analysis. Unknown behavior stays possibly non-terminating; an annotation cannot certify an arbitrary program. Pure computation may still loop, while finite computation may still panic. Local mutation and effects handled entirely inside the invocation remain compatible with outward purity.

A budget changes one evaluation into a finite attempt; it does not prove the unbounded action terminates. Deterministic charged events make the allowance independent of elapsed time. Complete coverage matters more than whether the source looks pure: an external call with an empty effect row can still remain outside the budget's control. For that reason, bodyless external declarations provide neither termination evidence nor budget eligibility.

Exhaustion ends the protected computation before requesting an ordinary abortive effect. Recovery can introduce its own effects, state, or divergence, so handling exhaustion alone cannot establish a `halt` contract. Finite cleanup has an independent obligation and cannot be skipped because the main computation used its last unit. An inner allowance cannot refill an outer one, and a returned closure cannot carry a finished invocation's allowance into a future call.

### Parameterized Handlers and Budget Configuration

```ril
with Div::exhausted() -> None
with Div::budget(10_000)
Some(search())
```

The two forms serve different roles: an operation arm describes a response to a request, while a parameterized application supplies configuration to a scoped computation. A general `with f(args)` passes the remainder of the block as a final anonymous callable. Budget configuration therefore uses the same form as other parameterized handlers, without turning an operation's resumption value into a special configuration channel.

Ordinary closure semantics remain applicable, including lexical handler selection, escape checks, and the callable's return target. This keeps the compact form equivalent to its explicit call. A wrapper can discharge still-forwarded effects but cannot rebind a handler already selected by the action. The finite-evaluation guarantee belongs to the built-in `Div::budget` contract, not to arbitrary wrappers that happen to count operations.

Koka's [generalized with statements and abstracted handlers](https://koka-lang.github.io/koka/doc/book.html) provide a reference for the application form and for operation-counting handlers. Such counting does not establish coverage of arbitrary loops. Chez Scheme's [finite-allowance computation interface](https://cisco.github.io/ChezScheme/csug10.3.0/control.html) separates an allowance from completion and expiration; Ril's termination guarantee additionally requires that an exhausted computation cannot be indefinitely resumed or refilled. Static meta/type budgets retain their separate role as limits on individual symbolic evaluations, not evidence that an unbounded definition terminates.

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

Task safety follows actual permissions, origins, and immutable data rather than a separate set of nominal marker traits. A simple visible type cannot hide a closure's or aggregate's live state from verification. Resource transfer and confined parallel writes have explicit contracts rather than weakening the general boundary rule.

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

The concise closure syntax does not require a separate handler-capture list. Retained handler environments remain part of the machine's provenance and authority checks. Their reads, writes, sharing, and task restrictions survive effect handling and can be expanded in diagnostics just like an ordinary closure's captures.

Operation dispatch reuses ordinary `match` for request values. Ending temporary loans at `resume` avoids assuming caller resources survive the continuation; outer loans still prevent reentrant aliasing.

### Effect-Free Data Parallelism

```ril
halt fn squares(values: []f64) -> []f64 {
    values |> Parallel::map(\x -> x * x)
}
```

Independent evaluation does not require a new control-request effect named Parallel. The callback's residual effects must be empty and its computation must separately be proved finite, though local handling and immutable captures remain useful. A finite budget inside a callback can establish the latter when its recovery also terminates. A fixed 64-element reduction tree supplies its own reference semantics; it is not ordinary left-fold equivalence or a claim that floating addition is associative.

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

Consuming detached tickets on every send outcome gives failure a closing action without rollback. Transport success does not settle a payload's business-error inspection duty.

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

Structural equality avoids callbacks and allocation identity. Value-only keys preserve clone/derive permissions; floats are excluded because NaN equality is not reflexive. Insertion order needs no implicit comparator.

### One Lexical Namespace

```ril
use math/geometry                     -- Binds Geometry
-- type Geometry = int                -- Error [E0203]: same-scope name already exists
```

One declaration can have type/constructor roles, or Set's type/namespace roles, without a second import dialect. Qualified variants permit repeated labels across sums; unique abbreviations keep common code short without type-directed name resolution.

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
assert(result is Ok(_))
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
assert(reply is Ok(_))
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

Casing makes constructor tests, variable bindings, types, and constants distinguishable at their use sites. All-caps belongs to static/top-level immutable constants, not mutable state; acronyms use title casing and module paths use snake_case. Static-key binders and generated schema labels use distinct casing roles without weakening ordinary variable rules.

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
fn get_field<T: { ..R }, K: keyof T>(record: T, key: K) -> T.(K) { record.(key) }
```

Static keys preserve record access without promoting run-time strings. Sum keys describe possible payload types; matching selects the actual payload.

Callable effects belong to values, so type-name purity reflection would conflict with omitted-row inference. Static values and shape queries suffice for branch selection.

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
pub type DomError {
    ElementNotFound,
    SecurityViolation(str),
}
pub fn read_attribute(elem: DomElement, key: str) -> Result<?str, DomError> @Fiber
```

The Ril contract remains the source of typing, effect, permission, and failure guarantees at an external boundary. Declaration units reuse ordinary syntax instead of adding foreign-only keywords or untyped escape types. Opaque handles prevent structural penetration; host failures must respect typed domain-error or supervised-panic contracts rather than leak a second error model.

A bodyless external declaration cannot establish that its host implementation tells the truth about that contract. This is an explicitly delimited trust boundary, not a general permission for application code to suppress provenance checks. Ordinary Ril code remains checked against the declared boundary contract and all origins and permissions that cross it.

Termination has no corresponding foreign assertion: a bodyless function remains possibly non-terminating and cannot be made budget-covered by annotating it. Verified Ril definitions imported from another module and language-defined finite primitives have their own evidence; merely declaring an external function pure supplies none.

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
type PureInvoker = fn(Action) -> () @{} &{} -- Empty rows belong to the higher-order arrow
```

A callable combines input/output shapes, access obligations, and control effects, and can itself be stored as data. Simplified types should not expose every captured variable, but must preserve its obligations. Named definitions declare concrete invocation state and effects, including known dependencies from calls; symbolic callback forwarding never changes parameter modes. Admitted higher-order empty rows constrain the total invocation domain, while omitted callable-type rows retain actual inferred obligations.

```ril
var count = 0
fn advance() &{mut count} { count += 1 }
let action = advance
```

A named function with external-state obligations need not own a mutable captured environment. Its function value can be immutable while invocation still writes the named external origin. Conversely, `&closure` can hide private environment names without hiding their actual permission facts from verification. Ordinary return types and calls keep source compact; expanded diagnostics provide the omitted detail.

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

The table describes obligations surviving the enclosing frame. Local aliases, stores, and destructuring of existing writable handles still need their `^mut` markers. Lexical captures and ordinary returns remain inferred; an explicit `^mut` parameter/argument and matching retention capability already cover the corresponding boundary publication. A fresh ordinary clone may preserve repeated references inside its result graph: writable reception requires `^mut clone(value)` when internal writable aliases are possible (`E0510` if omitted), and exclusivity still checks those aliases. A factory's `&^mut` describes a new publication, not the mere presence of already shared state in a closure it invokes or forwards. Existing sharing remains tracked even when that invocation publishes nothing new.

```ril
type Step = fn() -> int &closure
fn make_shared_step(^mut cell: Cell) -> Step &capture &^mut {
    \-> { cell.count += 1; cell.count }
}

let mut cell = Cell.{ count: 0 }
let mut step = make_shared_step(^mut cell)
assert(step() == 1)
cell.count += 1
assert(step() == 3)
```
