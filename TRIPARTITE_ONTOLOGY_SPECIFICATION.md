# Ril Language Specification: Tripartite Ontology & Asymmetric Domain Architecture

**Status:** Canonical Language Design Specification & Architectural Foundation  
**Version:** 0.1.0  
**Format:** Code-First Normative Document  

---

## 1. Executive Summary & Foundational Ontology

The Ril programming language rejects the historical conflation of data layout, memory access permissions, and dynamic control transfer. Instead, Ril establishes a mathematically rigorous, stratified **Tripartite Ontology**:

```
+---------------------------------------------------------------------------------------------------+
|                                      THE TRIPARTITE ONTOLOGY                                      |
+---------------------------------------------------------------------------------------------------+
|  Domain I: Data & Shape (T)         |  Domain II: Storage & Access (C)    |  Domain III: Control & Transfer (E) |
|  - Types at rest                    |  - Storage cell permissions         |  - Stack-delimited control flows    |
|  - Value vs Reference types         |  - Three-tier mutability            |  - Algebraic effects ('eff')        |
|  - Records, Arrays, Tuples, Sums    |  - Parameter modes ('mut')          |  - Handlers ('with')                |
|  - Nominals & Opaque types          |  - Capability tracking (&mut, &^mut)|  - Affine resumption ('resume')     |
|  - Field 'mut' (interior marker)    |  - Aliasing exclusivity             |  - Built-ins (@Async, @Fiber, @Div) |
+-------------------------------------+-------------------------------------+-------------------------------------+
                                                       |
                                                       v
                                    +-------------------------------------+
                                    |     COMPUTATION CONFLUENCE (fn)     |
                                    |   fn(P) -> R  @Eff  &Cap            |
                                    | - P in T (parameters at rest)       |
                                    | - R in T (return shape at rest)     |
                                    | - @Eff in E (latent control flow)   |
                                    | - &Cap in C (latent access rights)  |
                                    +-------------------------------------+
```

### 1.1 The Three Disjoint Semantic Domains

```
   Semantic Domains = < Shape (Type), Access (Capability), Control (Effect) >
```

1. **Domain I: Data & Shape Domain ($\mathcal{T}$)**:
   - **Metaphysical Nature**: Memory representation, data alignment, structural topology, and nominal identity of values in *normal form* (quiescent data at rest).
   - **Syntactic Locus**: Values, expressions, variables, data structures, and function parameter/return types.
   - **Constituents**:
     - *Primitive Value Types*: `bool`, `i8`, `i16`, `i32`, `i64`, `u8`, `u16`, `u32`, `u64`, `int`, `bigint`, `f32`, `f64`, `str`, `bytes`, `()`, `never`.
     - *Heap Reference Types*: Structural records `{...}`, linear arrays `[]T`, associative maps `[K: V]`, unique sets `Set<T>`, anonymous tuples `(...)`.
     - *Algebraic Sum Types & GADTs*: `type Option<T> { Some(T), None }`.
     - *Nominal Wrappers & Unit Nominals*: `type UserId(int)`, `type Marker`.
     - *Opaque Types*: `pub opaque type SessionToken = str`.
   - **Structural Field Modifier**: The record field modifier `mut` (e.g. `{ mut val: int }`) is strictly an interior mutability layout marker of a heap reference cell. It is **not** an operational capability.
   - **Axiom of Inactivity**: Types are inert shapes. A type cannot perform computation, yield execution control, hold ambient access capabilities, or trigger algebraic side effects.

2. **Domain II: Storage & Access Domain ($\mathcal{C}$)**:
   - **Metaphysical Nature**: Static tracking of heap mutation authority, storage cell access rights, pointer stability, and aliasing exclusivity. It specifies *what memory an activation frame or handle is permitted to mutate, reassign, or retain*.
   - **Syntactic Locus**: Variable bindings (`let`, `let mut`, `var`, `let view`), function parameter modes (`p: T`, `mut p: T`), and callable capability qualifiers (`&mut`, `&^mut`, `&closure`, `&capture`, `&{ident}`, `&{mut ident}`).
   - **Guarantees**: Governed by the Law of Exclusivity, Monotonic Permission Degradation, and Anti-Laundering theorems (`E0520`–`E0528`), preventing hidden aliasing, pointer invalidation, and data races without marker traits or lifetime annotations.
   - **Axiom of Non-Reification**: Capabilities are operational permissions, not data values. A capability cannot be instantiated at runtime, bound to a variable, stored in a collection, or aliased as a standalone type.

3. **Domain III: Control & Transfer Domain ($\mathcal{E}$)**:
   - **Metaphysical Nature**: Dynamic control inversion, delimited continuation interception, stack unwinding protocols, and cooperative fiber scheduling. It specifies *what non-local control transfers and ambient runtime requests can occur during the reduction of an expression*.
   - **Syntactic Locus**: **Exclusively confined to Computation / Arrow Signatures** (`fn(P) -> R @Eff &Cap`), effect declarations (`eff`), and handler blocks (`with`).
   - **Constituents**:
     - *Algebraic Effect Definitions*: `eff FileIo { read() -> str }`.
     - *Stack Handlers*: `with Handler { op(args) -> ... }`.
     - *Affine Resumptions*: `resume value`.
     - *Built-in Effect Sub-Lattice*: `@Fiber` (cooperative leaf I/O quantum) $\subset$ `@Async` (compound concurrency alias) $\equiv \{\text{Fiber}, \text{Concurrent}\}$, disjoint from `@Div` (divergence).
   - **Axiom of Delimited Execution**: Effects represent active computational protocols between code and ambient stack handlers. Once an expression is reduced to normal form, its effects have transpired; evaluated values carry zero latent effects.

---

### 1.2 The Computation Confluence Point ($\mathbf{fn}$)

The three domains are mutually exclusive and never mix directly. They converge **exclusively** at the **Computation Boundary**: the first-class callable arrow:

$$\tau_{\text{callable}} = \mathbf{fn}(P_1, \dots, P_n) \to R \ [@\mathcal{E}] \ [\,\&\mathcal{C}\,]$$

```ril
-- The Computation Confluence in Action:
--   Parameters (Domain I: Shape)
--   Return Type (Domain I: Shape)
--   Latent Effects (Domain III: Control)
--   Latent Capabilities (Domain II: Access)
type SocketHandler = fn(mut buffer: []u8, timeout_ms: int) -> Result<int, IoError> @Fiber &mut
```

- **Why Confluence Occurs Here**: A function, closure, or thunk is an unevaluated, suspendable computation. It mediates between input/output data shapes ($P \in \mathcal{T}, R \in \mathcal{T}$), ambient control transfers ($@\mathcal{E} \subseteq \mathcal{E}$), and storage access permissions ($\&\mathcal{C} \subseteq \mathcal{C}$).
- **First-Class Closure Property**: Because $\tau_{\text{callable}}$ is itself a first-class type in Domain I ($\tau_{\text{callable}} \in \mathcal{T}$), callable types can be stored in records, passed as variant payloads, nested in tuples, or aliased under `type T = ...`.

---

## 2. Boundaries of Type Definitions (`type T = ...`)

### 2.1 What Type Definitions CAN Contain (Supported)

1. **Structural Product Shapes & Interior Mutability**:
   - Record definitions with field-level interior mutability: `{ mut val: int, tag: str }`.
   - *Normative Distinction*: `mut field: T` designates an interior mutable offset within a heap allocation. It does not carry capability semantics until accessed via a pinned mutable handle (`let mut`) or borrowed parameter (`mut`).
2. **First-Class Callable Signatures**:
   - Nested function arrows carrying latent effects and capabilities: `fn(In) -> Result<Out, Err> @Fiber + Async &mut`.
3. **Algebraic Sum Variants & GADTs**:
   - Constructors with positional payloads `Some(T)`, record payloads `Record{ x: int }`, or constructor equations `Lit(int) -> Expr<int>`.
   - Variants holding callable types: `Handler(fn(Event) -> () @Io)`.
4. **Nominal Wrappers & Unit Nominals**:
   - `type UserId(int)`, `type Marker`.
5. **Opaque Type Representations**:
   - `pub opaque type SessionToken = str`.
6. **Pure Compile-Time Type Functions**:
   - `halt type Transform<T> = ...` (strictly pure compile-time functions returning `type<T>`).

---

### 2.2 What Type Definitions CANNOT Contain (Strictly Forbidden)

Ril statically rejects six structural anti-patterns that attempt to break domain isolation:

| # | Forbidden Anti-Pattern | Semantic Domain Violation | Diagnostic Code | Diagnostic Identifier |
| :-: | :--- | :--- | :-: | :--- |
| **1** | Bare effect aliases (`type E = @Io`) | Attempting to alias Domain III (Control) as Domain I (Data) | **`E0330`** | `BareEffectTypeAliasError` |
| **2** | Bare capability aliases (`type C = &mut`) | Attempting to alias Domain II (Access) as Domain I (Data) | **`E0331`** | `BareCapabilityTypeAliasError` |
| **3** | Direct variant computation annotations (`type S = Init @Async`) | Injecting Domain II/III onto Domain I data constructor tags | **`E0332`** | `VariantComputationAnnotationError` |
| **4** | Direct field computation annotations (`type C = { f: str @Io }`) | Injecting Domain II/III onto Domain I passive storage slots | **`E0333`** | `FieldComputationAnnotationError` |
| **5** | Generic computation constraints (`<T: @Io>`, `<T: &mut>`) | Constraining Domain I type parameters by Domain II/III | **`E0334`** | `GenericComputationConstraintError` |
| **6** | Type function computation annotations (`halt type F<T> = ... @Io`) | Polluting compile-time symbolic evaluation with runtime effects/caps | **`E0335`** | `TypeFunctionComputationAnnotationError` |

---

### 2.3 Code-First Normative Rules & Contrast Matrix

#### 1. Bare Effect Aliases (`E0330`) vs. `eff` Declarations
Effects represent stack-delimited control protocols. They are declared and combined strictly via `eff`. They cannot be defined via `type`.

```ril
-- Prohibited: Bare Effect Type Aliasing (E0330)
-- type BadEffect = @Io                         -- Error [E0330]: bare effect '@Io' cannot be aliased as a type; declare effects using 'eff'
-- type CombinedEffect = @Io + Async            -- Error [E0330]: bare effect row '@Io + Async' cannot be aliased as a type; combine effects via 'eff'
-- type DynamicEff = @Fiber                     -- Error [E0330]: bare effect '@Fiber' cannot be used in type definition

-- Compliant: Declared via 'eff' and combined via 'eff'
eff Io {
    read_line() -> str,
    write_line(str) -> (),
}

eff AsyncIo { Io, Fiber }                      -- OK: effect set combination declared via 'eff'

-- Compliant: Decorating the callable confluence arrow
type ReaderFn = fn() -> str @Io                -- OK: effect annotates callable arrow
type AsyncWorker<T> = fn(T) -> () @AsyncIo     -- OK: effect annotates callable arrow
```

#### 2. Bare Capability Aliases (`E0331`) vs. Interior Mutability Markers
Capabilities represent dynamic permissions over storage locations. They cannot be aliased as types.

```ril
-- Prohibited: Bare Capability Type Aliasing (E0331)
-- type BadMut = &mut                           -- Error [E0331]: bare capability '&mut' cannot be aliased as a type; capabilities belong to storage and callable domains
-- type BadShare = &^mut                        -- Error [E0331]: bare capability '&^mut' cannot be aliased as a type
-- type BadGlobal = &{mut app_cache}            -- Error [E0331]: bare capability '&{mut app_cache}' cannot be aliased as a type
-- type BadClosure = &closure                   -- Error [E0331]: bare capability '&closure' cannot be aliased as a type

-- Compliant: Structural interior mutability marker on heap record
type StateNode = {
    mut count: int,                            -- OK: field 'mut' is a structural layout marker, not a capability
    tag: str,
}

-- Compliant: Decorating the callable confluence arrow
type Mutator<T> = fn(mut target: T) -> () &mut -- OK: capability annotates callable arrow
type SharedLogger = fn(str) -> () &closure &^mut -- OK: capability annotates callable arrow
```

#### 3. Sum Variant Computation Annotations (`E0332`) vs. Callable Payloads
Sum variants are passive data constructors producing tagged representations in memory. They are not active computations and cannot yield control or perform mutations.

```ril
-- Prohibited: Computation Annotations on Sum Variants (E0332)
-- type TaskStatus {
--     Pending,
--     Running @Async,                         -- Error [E0332]: sum variant 'Running' cannot declare algebraic effect '@Async'; variants are data constructors, not computations
--     Mutating &mut,                          -- Error [E0332]: sum variant 'Mutating' cannot declare state capability '&mut'; variants are data constructors, not computations
--     Suspended(int) @Fiber,                  -- Error [E0332]: sum variant 'Suspended' cannot declare algebraic effect '@Fiber'
-- }

-- Compliant: Variants holding callable payloads
type TaskStatus {
    Pending,                                   -- OK: nullary data constructor tag
    Running(fn() -> () @Async),                -- OK: payload is a callable arrow encapsulating computational effect
    Mutating(fn(mut StateNode) -> () &mut),    -- OK: payload is a callable arrow encapsulating mutation capability
    Suspended({ duration_ms: int }),           -- OK: pure record payload
    Completed(int),                            -- OK: pure scalar payload
}

let status: TaskStatus = Running(\-> {
    Async::sleep(100)
})                                             -- OK: constructs data variant holding callable thunk
```

#### 4. Record Field Computation Annotations (`E0333`) vs. Callable Fields
Record fields store data values at rest. They cannot be decorated with effects or capabilities.

```ril
-- Prohibited: Computation Annotations on Record Fields (E0333)
-- type BadChannel = {
--     stream: str @Io,                        -- Error [E0333]: record field 'stream' cannot declare algebraic effect '@Io'; fields store values or callables
--     buffer: []u8 &mut,                      -- Error [E0333]: record field 'buffer' cannot declare state capability '&mut'; use 'mut' prefix or callable arrow
--     sink: int &{mut app_cache},             -- Error [E0333]: record field 'sink' cannot declare external state capability
-- }

-- Compliant: Field interior mutability & callable fields
type ValidChannel = {
    mut buffer: []u8,                          -- OK: 'mut' prefix marks heap interior mutability
    stream: fn() -> str @Io,                   -- OK: field stores a callable arrow carrying algebraic effect
    writer: fn(mut []u8) -> () &mut,           -- OK: field stores a callable arrow carrying state capability
}

let mut ch = ValidChannel.{
    buffer: [],
    stream: \-> Io::read_line(),
    writer: \mut buf -> { buf !> Array::push(0) },
}
ch.buffer !> Array::push(42)                   -- OK: mutate interior mutable field via 'let mut' root
```

#### 5. Generic Computation Constraints (`E0334`) vs. Automatic Forwarding
Generic parameters parameterize types (`Type`, `Type -> Type`) or compile-time values (`SnakeCase: ValueType`). They do not parameterize or constrain effects or capabilities. Higher-order functions forward effects and capabilities automatically.

```ril
-- Prohibited: Generic Computation Constraints (E0334)
-- fn bad_exec<T: @Io>(task: T) -> () {        -- Error [E0334]: generic parameter 'T' cannot be constrained by algebraic effect '@Io'; generics parameterize types or values
--     task()
-- }
-- type BadWrapper<T: &mut> = { item: T }      -- Error [E0334]: generic parameter 'T' cannot be constrained by state capability '&mut'
-- fn bad_pipe<T: @Async + Io>(x: T) -> T {    -- Error [E0334]: generic parameter 'T' cannot be constrained by effect row '@Async + Io'
--     x
-- }

-- Compliant: Higher-Order Functions automatically forward latent @Eff and &Cap
fn execute<T, R>(task: fn(T) -> R, arg: T) -> R {
    task(arg)                                  -- OK: automatically forwards callee's effects and capabilities
}

-- Compliant: Generic type parameter constrained by structural record shape
fn log_id<T: { id: int, ..R }>(item: T) -> int {
    item.id                                    -- OK: row constraint is a shape property
}

-- Compliant: Generic type parameter constrained by keyof
fn get_field<T, K: keyof T>(record: T, key: K) -> T.(K) {
    record.(key)                               -- OK: keyof constraint is a shape property
}
```

#### 6. Pure Type Function Computation Annotations (`E0335`) vs. Symbolic Purity
Pure type functions (`halt type`, `type F = \T -> ...`) evaluate strictly within the compile-time symbolic domain ($\mathbf{Eff} = \emptyset, \mathbf{Cap} = \emptyset$). They produce static types (`type<T>`). They cannot declare runtime effects or capabilities.

```ril
-- Prohibited: Type Function Computation Annotations (E0335)
-- halt type BadTransform<T> = \T -> type<T> @Io    -- Error [E0335]: pure type function 'BadTransform' cannot declare algebraic effect '@Io'; type functions are axiomatically pure
-- type BadMapper<T> = \T -> type<T> &mut           -- Error [E0335]: pure type function 'BadMapper' cannot declare state capability '&mut'
-- halt type BadAsyncType<T> = \T -> type<T> @Async &closure -- Error [E0335]: pure type function cannot declare effects or capabilities

-- Compliant: Pure compile-time type functions returning type<T>
halt type MakeNullable = \T -> {
    type<?T>                                   -- OK: pure type evaluation returning type<T>
}

halt type SafeRecord = \T -> {
    if typeof(T) == typeof(int) {
        type<{ val: int, valid: bool }>
    } else {
        type<{ val: T, valid: bool }>
    }
}

type NullableInt = MakeNullable<int>           -- Resolves to ?int
type IntRecord   = SafeRecord<int>             -- Resolves to { val: int, valid: bool }
```

---

## 3. The Storage & Access Domain: Capability Tracking

### 3.1 The Three-Tier Mutability Architecture & Live Views

Ril decomposes storage mutability into a 2×2 matrix, cleanly separating slot reassignment from interior heap mutation:

| Binding Form | Variable Reassignment (`x = ...`) | In-Place Mutation (`x.f = ...`, `x !> ...`) | Storage Semantics | Mental Model & Lifetime Invariants |
| :--- | :---: | :---: | :--- | :--- |
| **`let`** | [Prohibited] (`E0501`) | [Prohibited] (`E0520`) | **Immutable Binding** | Frozen snapshot, pure scalar copy, constant handle. |
| **`let mut`** | [Prohibited] (`E0502`) | [Permitted] ($\&mut$) | **Pinned Mutable Handle** | Fixed GC heap allocation; guaranteed pointer stability. |
| **`var`** | [Permitted] | [Permitted] ($\&mut$) / [Prohibited] (`E0520` if ReadOnly) | **Reassignable Variable** | Dynamic slot, loop accumulator, reassignable cursor. |
| **`let view`** | [Prohibited] (`E0501`) | [Prohibited] (`E0520`) | **Live Read-Only View** | Read-only observation window over a pinned mutable root. |

```ril
type UserDoc = { mut title: str, mut score: int }

-- 1. Immutable Binding ('let'):
let ro_val = 100
let ro_doc = UserDoc.{ title: "Guide", score: 50 }
-- ro_val = 200                         -- Error [E0501]: cannot reassign immutable binding 'ro_val'
-- ro_doc.score = 51                    -- Error [E0520]: cannot mutate field through read-only handle 'ro_doc'

-- 2. Pinned Mutable Handle ('let mut'):
let mut pinned_doc = UserDoc.{ title: "Draft", score: 0 }
pinned_doc.score = 10                  -- OK: in-place interior mutation permitted
pinned_doc.title = "Published"         -- OK: in-place field write permitted
-- pinned_doc = UserDoc.{ title: "New", score: 0 } -- Error [E0502]: cannot reassign pinned mutable handle 'pinned_doc'; use 'var'

-- Static Value Type Rejection on let mut (E0402):
-- let mut bad_scalar = 42             -- Error [E0402]: value type 'int' has no interior mutability; use 'var'

-- 3. Reassignable Mutable Variable ('var'):
var counter = 0
counter += 1                           -- OK: reassignable scalar
counter = 99                           -- OK: direct reassignment

var cursor_doc = pinned_doc            -- OK: reassignable reference variable
cursor_doc.score = 15                  -- OK: interior mutation permitted
cursor_doc = UserDoc.{ title: "Next", score: 100 } -- OK: handle reassignment permitted

-- 4. Live Read-Only View ('let view'):
let view observer = pinned_doc         -- OK: live view over pinned mutable root
assert(observer.score == 15)           -- OK: reads current state
pinned_doc.score = 20                  -- Mutate via root
assert(observer.score == 20)           -- OK: live view dynamically observes mutation
-- observer.score = 25                 -- Error [E0520]: cannot mutate through read-only view 'observer'

-- Invalid view targets:
-- let view bad_v1 = ro_doc            -- Error [E0531]: cannot create live view over immutable binding 'ro_doc' (source must be pinned mutable root)
-- let view bad_v2 = cursor_doc        -- Error [E0531]: cannot create live view over reassignable variable 'cursor_doc' (source must be pinned mutable root)

-- 5. Scoped Resource Bindings ('let scoped', 'let scoped mut'):
type Resource = { name: str, on_close: fn() -> () }
let mut cleanup_log: []str = []
{
    let scoped r1 = Resource.{ name: "R1", on_close: \-> cleanup_log !> Array::push("R1") }
    let scoped mut r2 = Resource.{ name: "R2", on_close: \-> cleanup_log !> Array::push("R2") }
    r2.name = "R2_updated"             -- OK: 'let scoped mut' allows in-place mutation
    -- r2 = Resource.{ name: "R3", on_close: \-> () } -- Error [E0502]: cannot reassign pinned scoped handle 'r2'
    -- var scoped bad = Resource.{ name: "B", on_close: \-> () } -- Error [E0532]: scoped bindings cannot be declared 'var'
}
assert(cleanup_log == ["R2", "R1"])    -- Strict LIFO exit order
```

---

### 3.2 Parameter Modes & Caller-Site Obligations

```ril
-- 1. Value Type Parameter: copy-by-value, local register isolated
fn process_scalar(val: int) -> int {
    val + 1                             -- OK: pure value copy
}
-- fn bad_mut_val(mut n: int) &mut {}  -- Error [E0401]: value types cannot be declared as 'mut' parameters
-- fn bad_var_val(var n: int) {}       -- Error [E0403]: 'var' parameters are prohibited in function signatures

-- 2. Read-Only Reference Parameter: shared read-only handle
fn inspect_doc(doc: UserDoc) -> str {
    -- doc.score += 10                  -- Error [E0520]: cannot mutate through read-only parameter 'doc'
    doc.title
}

-- 3. Borrowed Mutable Reference Parameter: borrows caller's heap storage
fn boost_score(mut doc: UserDoc, points: int) &mut {
    doc.score += points                 -- OK: in-place write through pinned mutable handle
    -- doc = UserDoc.{ title: "X", score: 0 } -- Error [E0502]: cannot reassign pinned parameter 'doc'
}

let mut active_doc = UserDoc.{ title: "Active", score: 10 }
let frozen_doc = UserDoc.{ title: "Frozen", score: 0 }

boost_score(mut active_doc, 5)          -- OK: explicit 'mut' at caller site
active_doc !> boost_score(10)          -- OK: mutating pipeline passes 'mut active_doc'

-- Caller-site anti-laundering rejections:
-- boost_score(active_doc, 5)          -- Error [E0520]: argument to 'mut' parameter must be passed with 'mut'
-- boost_score(mut frozen_doc, 5)      -- Error [E0520]: cannot borrow read-only handle 'frozen_doc' as 'mut'
-- fn noop_mut(mut doc: UserDoc) &mut {} -- Error [E0527]: 'mut' parameter 'doc' declared but never modified
```

---

### 3.3 The Law of Exclusivity & Cross-Argument Disjointness

Ril statically enforces disjointness across mutable parameters at call sites:

$$\forall i \in \mathrm{MutArgs},\quad \forall j \ne i,\quad \mathrm{Path}(a_i) \cap \mathrm{Path}(a_j) = \emptyset$$

```ril
type Account = { mut balance: int, mut credit: int }

fn transfer(mut src: Account, mut dst: Account, amt: int) &mut {
    src.balance -= amt
    dst.balance += amt
}

fn compare_and_audit(src: Account, mut dst: Account) &mut {
    dst.balance += src.balance
}

let mut acc1 = Account.{ balance: 1000, credit: 500 }
let mut acc2 = Account.{ balance: 200, credit: 0 }

transfer(mut acc1, mut acc2, 50)       -- OK: acc1 ∩ acc2 = ∅ (disjoint roots)

-- 1. Mut-Mut Aliasing Conflict (E0523):
-- transfer(mut acc1, mut acc1, 50)    -- Error [E0523]: MutMutAliasingConflictError: overlapping mutable arguments on 'acc1'

-- 2. Read-Mut Aliasing Hazard (E0524):
-- compare_and_audit(acc1, mut acc1)   -- Error [E0524]: ReadMutAliasingHazardError: 'acc1' borrowed mut while read-only borrowed

-- 3. Field Disjointness (Distinct fields of same struct):
fn adjust_fields(mut b: int, mut c: int) &mut { b += 1; c -= 1 }
adjust_fields(mut acc1.balance, mut acc1.credit) -- OK: acc1.balance ∩ acc1.credit = ∅ (statically disjoint fields)

-- 4. Dynamic Index Ambiguity (E0523):
let mut data = [10, 20, 30]
fn swap_elems(mut a: int, mut b: int) &mut { let t = a; a = b; b = t }
swap_elems(mut data[0], mut data[1])   -- OK: distinct constant indices 0 and 1
let i = 0; let j = 0
-- swap_elems(mut data[i], mut data[j]) -- Error [E0523]: dynamic indices may alias overlapping elements
```

---

### 3.4 Write Path Counting & Retained Mutable Sharing ($\mathcal{W}_{\text{surviving}}$)

The boundary between frame-confined mutation and surviving retained aliasing is governed by **Surviving Write Path Counting**:

$$\mathcal{W}_{\text{surviving}}(\text{origin}) \ge 2 \iff \&\hat{\;}\mathrm{mut}$$

```
                ┌──────────────────────────────────────────────────┐
                │          SURVIVING WRITE PATH COUNTING           │
                └─────────────────────────┬────────────────────────┘
                                          │
                  ┌───────────────────────┴───────────────────────┐
                  ▼                                               ▼
         W_surviving = 1                                 W_surviving ≥ 2
   (Encapsulated Private Cell)                     (Retained Mutable Sharing)
   ───────────────────────────                     ──────────────────────────
   • Stack frame terminates                        • Multiple persistent paths
   • Only the closure holds the cell               • Stashed in external container
   • Requires &capture, &closure                   • Requires &^mut, &{^mut ident}
   • &^mut rejected as EXCESSIVE (E0529)           • Omitting triggers E0510
```

```ril
type Ticker = { mut count: int }

-- 1. Encapsulated Allocation (W_surviving = 1):
-- Fresh heap record allocated inside frame and returned solely via escaping closure
fn make_ticker() -> (fn() -> int &closure) &capture {
    let mut fresh = Ticker.{ count: 0 }
    \-> {
        fresh.count += 1
        fresh.count
    }                                  -- OK: 1 surviving write path; declares &capture
}
-- fn bad_over_annotated() -> (fn() -> int &closure) &^mut { ... }
-- Error [E0529]: excessive capability '&^mut', private allocation has no surviving aliases

-- 2. Dual Escape (W_surviving = 2):
-- Both closure and direct handle escape into caller scope
fn make_dual_ticker() -> ((fn() -> int &closure), Ticker) &^mut {
    let mut fresh = Ticker.{ count: 0 }
    let runner = \-> { fresh.count += 1; fresh.count }
    (runner, fresh)                    -- Both escape: caller receives 2 write paths; MUST declare &^mut
}

-- 3. Intermediate Forwarding & Origin Invariance:
let mut external_ticker = Ticker.{ count: 0 }

fn make_forwarded() -> (fn() -> int &{mut external_ticker}) &{^mut external_ticker} {
    let mut forwarded = external_ticker -- Intermediate local handle does not launder origin
    \-> {
        forwarded.count += 1
        forwarded.count
    }                                  -- Tracks origin to 'external_ticker'; MUST declare &{^mut external_ticker}
}
-- Omitting capability triggers E0510:
-- fn bad_forwarded() -> (fn() -> int &{mut external_ticker}) { ... }
-- Error [E0510]: missing capability '&{^mut external_ticker}'
```

---

## 4. The Control & Transfer Domain: Algebraic Effects

### 4.1 Nature of Algebraic Effects & Deep Handlers (`with`)

Algebraic effects are abstract control-flow transfer tags intercepted by dynamically enclosing stack handlers:
1. **Dynamic Control Inversion**: When an effectful operation is invoked (`Eff::op(args)`), execution traverses *up* the call stack to locate the nearest dynamically enclosing handler established via `with`.
2. **Deep Handling**: Handlers in Ril are deep handlers. Invoking `resume v` supplies $v$ to the captured delimited continuation; the handler remains active for all subsequent effect invocations within that lexical block.
3. **Affine One-Shot Resumption (`resume`)**: The continuation handle is strictly affine ($\le 1$ invocation). Invoking `resume` more than once triggers `E0610`. Escaping `resume` beyond the lexical scope of the handler arm triggers `E0611`.
4. **Delimited Early Abort**: Returning from a handler arm without calling `resume` triggers an early abort. Delimited execution unwinds active `let scoped` resources in strict reverse allocation order (LIFO).
5. **Commit-on-Write Memory Semantics**: Physical memory mutations committed prior to an early abort remain permanently committed.

```ril
eff Query {
    fetch() -> int,
}

fn test_affine_resumption() -> int {
    with Query::fetch() -> {
        let first = resume 10           -- OK: first affine resumption
        -- let second = resume 20       -- Error [E0610]: affine resumption 'resume' invoked more than once
        first
    }
    Query::fetch()
}

fn test_escaping_resume() -> fn() -> int {
    with Query::fetch() -> {
        -- let esc = \-> resume 42      -- Error [E0611]: affine resumption 'resume' cannot escape handler arm
        -- esc
        resume 42                       -- OK: in-situ resumption
    }
    Query::fetch()
}
```

---

### 4.2 Built-in Effects and the Sub-Effect Lattice

Ril defines four foundational built-in effects forming a sub-effect lattice:

$$\emptyset \subset \{\text{Fiber}\} \subset \{\text{Fiber}, \text{Concurrent}\} \equiv \text{Async}, \quad \text{disjoint from } \{\text{Div}\}$$

```ril
-- 1. Least-Privilege Leaf I/O Principle (@Fiber):
fn read_leaf_socket(fd: int) -> []u8 @Fiber {
    Fiber::park()                       -- Relinquishes execution quantum until I/O ready
    Socket::drain(fd)                   -- OK: purely cooperative, leaf routine
}

-- Leaf @Fiber cannot fork structured concurrent tasks:
fn bad_leaf_concurrency(fd: int) -> []u8 @Fiber {
    -- scope(\mut s -> {                -- Error [E0612]: UnhandledEffectError: function declares '@Fiber' but invokes unhandled '@Concurrent' primitive 'scope'
    --     s.fork(\-> Socket::drain(fd))
    -- })
    read_leaf_socket(fd)
}

-- 2. Decoupling Untyped Quantum from Typed Streaming (@Yield<T>):
eff Yield<T> {
    emit(T) -> (),
}

fn number_generator(limit: int) -> () @Yield<int> {
    var i = 0
    while i < limit {
        Yield::emit(i)                  -- In-situ push-stream emission
        i += 1
    }
}

fn consume_stream() -> []int {
    let mut collected: []int = []
    with Yield::emit(v) -> {
        collected !> Array::push(v)
        resume ()
    }
    number_generator(5)
    collected                           -- OK: [0, 1, 2, 3, 4]
}
```

---

### 4.3 Structured Concurrency & Boundary Confinement

Structured concurrency guarantees the **Lifetime Containment Invariant**:
$$\forall c \in \text{Children}(S), \quad \mathop{\mathrm{Lifetime}}(c) \subseteq \mathop{\mathrm{Lifetime}}(S) \subset \mathop{\mathrm{Lifetime}}(\text{Frame}_{\text{parent}})$$

- **Zero-Heap Fast Path**: Intrusive child-stack descriptors allocate $O(1)$ scope tracking inline on each child fiber stack frame.
- **Synchronous Scope Unwind-Barrier**: Unwinders pause at the scope frame boundary until all child tasks complete or cancel.
- **Confinement Boundaries**:
  - `E0601: CrossThreadDataRaceHazardError`: Passing live mutable capabilities (`&mut`, `&^mut`, `&{mut var}`) or live views across concurrent task boundaries is statically rejected.
  - `E0615: CrossTaskUnhandledEffectError`: Concurrent child callables MUST be effect-closed under user-defined effects ($\mathop{\mathrm{Effects}} \subseteq \{\text{Fiber}\}$). Delimited continuations cannot span multiple independent fiber stacks.

```ril
use ril/concurrent::{scope, Scope, Task, TaskFault}

eff WorkerLog {
    write_log(str) -> (),
}

fn run_concurrent_boundary_test() -> Result<int, TaskFault> {
    with WorkerLog::write_log(msg) -> resume () -- Handler established on parent stack

    scope(\mut s -> {
        -- Prohibited: Unhandled effect cannot cross concurrent task boundary
        -- s.fork(\-> {
        --     WorkerLog::write_log("starting") -- Error [E0615]: CrossTaskUnhandledEffectError: concurrent task closure carries unhandled effect '@WorkerLog'; external handlers cannot cross task boundary
        -- })

        -- Compliant: Effect is handled locally within the child task activation:
        let worker = s.fork(\-> {
            with WorkerLog::write_log(msg) -> resume () -- Local deep handler on child stack
            WorkerLog::write_log("starting")            -- OK: discharged locally within child fiber
            100
        })

        let val = worker.join()?        -- OK: resolves to 100
        Ok(val)
    })
}
```

---

### 4.4 The Arrow-Only Law of Effects (`E0613`)

Computations reduce to values in normal form. Once reduced, no further control transfers can occur. Passive values carry Shape and Access, but **zero latent effects**.

Attaching `@Eff` annotations to value bindings, record fields, tuple elements, or arrays represents an ontological category error:

```ril
-- -----------------------------------------------------------------------------
-- Negative Examples: Prohibited Value Effect Annotations (E0613)
-- -----------------------------------------------------------------------------
-- type BadField = { data: int @Io }            -- Error [E0613]: record field has value type 'int'; raw effects cannot reside on values
-- type BadTuple = (str @Io, int)               -- Error [E0613]: tuple component has value type 'str'; raw effects cannot reside on values
-- type BadArray = []int @Async                 -- Error [E0613]: array element has value type 'int'; raw effects cannot reside on values

-- fn test_binding_error() @Io {
--     let bad_bind: str @Io = "hello"          -- Error [E0613]: binding 'bad_bind' specifies effect '@Io'; values in normal form carry no latent effects
--     let @Io bad_prefix = "hello"             -- Error [E0613]: binding pattern specifies effect '@Io'; misplaced effect annotation
-- }

-- -----------------------------------------------------------------------------
-- Positive Examples: Arrow-Only Law
-- -----------------------------------------------------------------------------
type ValidService = {
    name: str,                                  -- Pure value at rest
    fetch_data: fn() -> str @Io,                -- OK: callable arrow carrying latent effect
}

fn test_valid_binding() @Io {
    let result: str = Io::read_line()           -- OK: expression executes @Io; resulting value is pure 'str'
    assert(result != "")
}
```

---

## 5. The Asymmetric Scope of Influence

### 5.1 Why Capabilities CAN and MUST Govern Bindings

A variable binding is an access portal to physical storage in registers, the stack frame, or the GC heap. Memory is spatial and persistent. Every binding introduces an aliasing relationship. Therefore, capability tracking must govern:
1. **Reassignment Privilege**: Whether a binding slot can be overwritten (`var` vs `let`/`let mut`).
2. **Interior Write Privilege**: Whether fields reachable through a handle can be mutated in place (`let mut`/`var` vs `let`/`let view`).
3. **Live Observation**: Whether a handle dynamically observes background mutations of an aliased heap object (`let view`).
4. **Anti-Laundering Degradation**: Enforcing monotonic permission degradation ($\text{Mut} \succ \text{ReadOnly} \succ \text{None}$) across destructuring patterns, container insertions, and returns (`E0520`–`E0528`).

Capabilities attach directly to bindings because **bindings govern memory access permissions**.

---

### 5.2 Why Algebraic Effects NEVER Govern Bindings (Function & Data Colorlessness)

In contrast, algebraic effects govern **temporal, dynamic control transfers**:
1. An effect dispatch (`Console::print("hi")`, `Yield::emit(x)`) searches up the dynamic execution stack to locate an enclosing `with` handler.
2. Once an expression evaluates, its effect operations have **already been dispatched and handled**.
3. The resulting value is an **inert memory representation** in normal form. It contains no running threads, suspended stacks, or pending continuations.
4. If effects attached to bindings (e.g. `let @Async x = fetch()`), every struct field, array element, and tuple component would require viral effect colors. Ril preserves absolute **Function Colorlessness and Data Colorlessness**.

---

### 5.3 The Intersecting Boundary: Capability-Bearing Effect Operations

The definitive proof of Ril's Tripartite Ontology is an effect operation that mutates memory:

```ril
eff BufferIO {
    read_into(mut buf: []u8) -> int &mut,       -- Operation demands in-place buffer mutation
}
```

Here:
- The effect tag `BufferIO` governs **Control**: who intercepts the operation up the call stack.
- The capability annotation `&mut` governs **Access**: the operation demands write authority into the caller's mutable buffer.

The concerns remain strictly separated: the capability is verified via the storage domain; the effect is routed via the control domain.

---

## 6. Precise EBNF Grammar Formalization

```ebnf
(* ========================================================================= *)
(* 1. TYPE EXPRESSIONS (Domain I: Data & Shape)                              *)
(* ========================================================================= *)

TypeDecl         ::= [ "pub" ] [ "halt" ] "type" PascalCase [ GenericParams ] [ WhereClause ] "=" TypeExpression
OpaqueTypeDecl   ::= [ "pub" ] "opaque" "type" PascalCase [ GenericParams ] [ WhereClause ] "=" TypeExpression
NominalDecl      ::= [ "pub" ] "type" PascalCase [ GenericParams ] [ "(" TypeExpression ")" ] [ WhereClause ]
SumTypeDecl      ::= [ "pub" ] "type" PascalCase [ GenericParams ] [ WhereClause ] "{" VariantDeclList "}"

TypeExpression   ::= PrimaryType
                   | RecordType
                   | TupleType
                   | ArrayType
                   | MapType
                   | SetType
                   | CallableType
                   | TypeProjection
                   | TypeFunctionExpr

PrimaryType      ::= PrimitiveType | NominalRef | "(" TypeExpression ")"
NominalRef       ::= PascalCase [ GenericArgs ]

(* Callable Type: THE CONFLUENCE POINT *)
CallableType     ::= "fn" "(" [ ParameterTypeList ] ")" [ "->" TypeExpression ] [ EffectAnnot ] [ StateAnnot ]
ParameterTypeList::= ParameterTypeItem { "," ParameterTypeItem } [ "," ]
ParameterTypeItem::= [ "mut" ] [ SnakeCase ":" ] TypeExpression

(* Records: 'mut' is exclusively a prefix layout marker on fields *)
RecordType       ::= "{" [ RecordFieldList ] "}"
RecordFieldList  ::= RecordField { "," RecordField } [ "," ] [ ".." SnakeCase ]
RecordField      ::= [ "mut" ] SnakeCase ":" TypeExpression

(* Sum Types: Variants are pure data constructors *)
VariantDeclList  ::= VariantDecl { "," VariantDecl } [ "," ]
VariantDecl      ::= PascalCase [ GenericParams ] [ VariantPayload ] [ "->" TypeExpression ]
VariantPayload   ::= "(" VariantFields ")" | "{" RecordFieldList "}"
VariantFields    ::= VariantField { "," VariantField } [ "," ]
VariantField     ::= [ SnakeCase ":" ] TypeExpression

(* Generic Parameters: Strictly Types or Const Values *)
GenericParams    ::= "<" GenericParamDecl { "," GenericParamDecl } [ "," ] ">"
GenericParamDecl ::= TypeParamDecl | ConstParamDecl
TypeParamDecl    ::= PascalCase [ ":" TypeSort ] [ "=" TypeExpression ]
ConstParamDecl   ::= SnakeCase ":" ValueType [ "=" Expression ]
TypeSort         ::= "Type" | KindSignature | RecordConstraint | KeyofConstraint
KindSignature    ::= "Type" "->" ( "Type" | KindSignature )
RecordConstraint ::= "{" [ RecordConstraintField { "," RecordConstraintField } [ "," ] ] ".." SnakeCase "}"
RecordConstraintField ::= [ "mut" ] SnakeCase ":" TypeExpression
KeyofConstraint  ::= "keyof" TypeExpression

(* ========================================================================= *)
(* 2. CONTROL & TRANSFER DOMAIN (Domain III: Algebraic Effects)              *)
(* ========================================================================= *)

EffectDecl       ::= [ "pub" ] "eff" PascalCase [ GenericParams ] "{" EffectMemberList "}"
EffectMemberList ::= ( EffectOpDecl { "," EffectOpDecl } [ "," ] )
                   | ( PascalCase { "," PascalCase } [ "," ] )
EffectOpDecl     ::= SnakeCase "(" [ ParameterList ] ")" [ "->" TypeExpression ] [ StateAnnot ]
EffectAnnot      ::= "@" EffectRow
EffectRow        ::= EffectIdentifier { "+" EffectIdentifier }
EffectIdentifier ::= PascalCase [ GenericArgs ]

(* ========================================================================= *)
(* 3. STORAGE & ACCESS DOMAIN (Domain II: Capabilities)                      *)
(* ========================================================================= *)

StateAnnot       ::= StateCapability { StateCapability }
StateCapability  ::= "&mut"
                   | "&^mut"
                   | "&closure"
                   | "&capture"
                   | "&{" [ "^" ] "mut" SnakeCase "}"
                   | "&{" SnakeCase "}"
```

---

## 7. Diagnostic Error Codes Summary & Verification Matrix

| Code | Diagnostic Identifier | Category | Formal Violation Condition |
| :---: | :--- | :--- | :--- |
| **`E0309`** | `VacuousBindingError` | Storage | `let` pattern introduces zero variable bindings (excluding `let _ = expr`). |
| **`E0330`** | `BareEffectTypeAliasError` | Ontology | Attempting to alias an effect (`@Eff`) under `type E = ...`. Declare effects via `eff`. |
| **`E0331`** | `BareCapabilityTypeAliasError` | Ontology | Attempting to alias a capability (`&mut`, `&^mut`) under `type C = ...`. |
| **`E0332`** | `VariantComputationAnnotationError` | Ontology | Attaching `@Eff` or `&Cap` directly to a sum type variant constructor. |
| **`E0333`** | `FieldComputationAnnotationError` | Ontology | Attaching `@Eff` or `&Cap` directly to a record field or tuple component. |
| **`E0334`** | `GenericComputationConstraintError` | Ontology | Constraining a generic parameter with an effect (`<T: @Io>`) or capability (`<T: &mut>`). |
| **`E0335`** | `TypeFunctionComputationAnnotationError`| Ontology | Declaring `@Eff` or `&Cap` on a pure compile-time type function (`halt type`). |
| **`E0401`** | `ValueTypeMutableBorrowError` | Storage | Attempting to declare or pass a value type as `mut` parameter, or giving `mut` param a default value. |
| **`E0402`** | `ValueTypePinnedMutError` | Storage | Attempting to bind a value type to pinned mutable handle `let mut`. |
| **`E0403`** | `VarParameterProhibitedError` | Storage | Declaring a function parameter with `var`. |
| **`E0501`** | `ImmutableReassignmentError` | Storage | Reassigning an immutable `let` or `let view` binding. |
| **`E0502`** | `PinnedHandleReassignmentError` | Storage | Reassigning a `let mut` pinned handle, `let scoped mut`, or borrowed `mut` parameter. |
| **`E0510`** | `MissingCapabilityAnnotationError` | Storage | Mutating state, parameters, or external origins without declaring required `&mut` or `&^mut`. |
| **`E0520`** | `MutabilityLaunderingError` | Storage | Binding/assigning read-only handle to `let mut`/mutable `var`, passing read-only to `mut` param, or mutating view. |
| **`E0521`** | `DestructureMutabilityLaunderingError`| Storage | Destructuring a read-only record into `mut` or `var` pattern fields. |
| **`E0522`** | `ContainerMutabilityLaunderingError` | Storage | Injecting a read-only reference into a mutable collection. |
| **`E0523`** | `MutMutAliasingConflictError` | Storage | Overlapping mutable arguments passed to `mut` parameters or captured in arguments. |
| **`E0524`** | `ReadMutAliasingHazardError` | Storage | Mutable argument aliases simultaneous read-only argument or callback capture. |
| **`E0525`** | `SpreadLaunderingError` | Storage | Shallow-spreading a read-only record into a `let mut` or mutable `var` root. |
| **`E0526`** | `CollectionMutationDuringIterationError`| Storage | Mutating a collection in place while iterating over it in a `for` loop. |
| **`E0527`** | `UnusedMutableBindingError` | Storage | `var`, `let mut`, or `mut` parameter never modified along any reachable executable path. |
| **`E0528`** | `ReturnMutabilityLaunderingError` | Storage | Returning a read-only parameter into caller `let mut` or mutable `var` handle. |
| **`E0529`** | `ExcessiveCapabilityAnnotationError` | Storage | Over-annotating signature beyond minimal required capabilities (e.g. `&^mut` on private allocation). |
| **`E0530`** | `IllegalCapabilityCloneImmutError` | Storage | Passing a target carrying active capabilities or scoped handles to `clone` or `clone_immut`. |
| **`E0531`** | `ImmutableTargetViewError` | Storage | Creating `let view` over an immutable `let` binding or reassignable `var`. |
| **`E0532`** | `ReassignableScopedResourceError` | Storage | Declaring a scoped resource with `var scoped` or `scoped var`. |
| **`E0533`** | `AliasedNarrowingHazardError` | Storage | Narrowing a `var` binding aliased by a live view or captured in a mutable closure. |
| **`E0601`** | `CrossThreadDataRaceHazardError` | Concurrency | Passing live mutable capabilities or live views across concurrent task boundaries. |
| **`E0610`** | `DuplicateResumeInvocationError` | Control | Invoking affine one-shot resumption `resume` more than once. |
| **`E0611`** | `EscapingResumeError` | Control | Escaping resumption handle beyond handler arm lexical scope. |
| **`E0612`** | `UnhandledEffectError` | Control | Invoking effect operation without in-scope handler or declaring effect in callable signature. |
| **`E0613`** | `ValueEffectAnnotationError` | Control | Attaching algebraic effect annotation (`@Eff`) to a non-callable type expression or value binding. |
| **`E0614`** | `EscapingEffectClosureError` | Control | Closure with unhandled effect escaping to heap record without in-scope handler. |
| **`E0615`** | `CrossTaskUnhandledEffectError` | Control | Passing callable with unhandled effect across concurrent task boundary. |
| **`E0616`** | `ScopedCleanupEffectError` | Control | Resource cleanup handler (`on_close`) declares or invokes unhandled algebraic effects. |
| **`E0617`** | `ScopedCleanupDivergenceError` | Control | Resource cleanup handler (`on_close`) declares or invokes divergent operations (`@Div`). |
| **`E0618`** | `UndischargedLocalEffectError` | Control | Local algebraic effect declared in 'where' is not completely discharged within enclosing block. |
