# The Ril Standard Library Specification

**Version:** 0.1.0

**Status:** Canonical Standard Library Reference

**Format:** Code-First Normative Document

## Authority and Contract Notation

```ril
let words = "one,two" |> String::split(",")
assert(words == ["one", "two"])
use ril/array::{Elem}
type Word = Elem<[]str>
```

This document defines the public types, functions, effects, permissions, and observable behavior of the `ril/*` standard library.

Examples are independent fixtures unless marked complete. Local statements run inside an enclosing callable; free names are typed fixture inputs, not library exports. Complete programs include non-prelude imports.

| Annotation | Required outcome |
| :--- | :--- |
| `-- OK` | Valid program |
| `-- Error [EXXXX]` | Static rejection with the stated code |
| `-- Warning [WXXXX]` | Valid program; warning is advisory |
| `-- Panics` | Run-time panic when evaluated |

Negative cases are checked separately with valid setup. Local fixture expressions have their required handlers; named functions obey their declared effects. Blocks containing `...` are schematic. Diagnostic message text is illustrative.

Signature blocks are interface extracts. Omitted bodies do not imply foreign calls. Opaque types use their stated data/resource classification. Listed signature families are closed library cases; user-defined overloading is not introduced. Unqualified names belong to the displayed module.

Unless a section states otherwise:

- Functions are ordinary run-time callables. Omitted effect/state rows introduce no concrete effects or external state; higher-order dependencies follow the actual callback. Read-only, `mut`, and `^mut` retain their language meanings.
- A fresh collection supplies fresh **outer storage**, not deep copies of its constituents. Projections, lookups, removals, and combinators preserve the returned values' provenance and inspection duties. A result is immutable only when the language's immutable-publication rule is satisfied. No operation silently freezes a live reference or upgrades a read-only element.
- Callbacks execute synchronously on the caller's task unless a concurrency contract says otherwise. Sequential combinators invoke them in source order, at most once per visited element; an abort stops subsequent invocations. They retain no callable after returning unless explicitly stated.
- Finite-data operations terminate when their callbacks and constituent operations terminate. Sequential callback entries and iteration steps consume active Div allowances. Iterators and waits retain their stated termination conditions.
- Invalid indexes or lengths supplied to assertive operations panic before mutation. Safe queries return `None`; domain failures return `Err`. Allocation exhaustion is an environmental limit, not a promise of a recoverable allocation API. No API guarantees a wall-clock bound.
- Complexity counts visited elements or bytes and excludes callback cost; equality, key comparison, and bigint costs must also be included when nonconstant. Stated bounds are requirements on observable work growth, not storage-layout requirements.

## Contents

- [Prelude and Module Index](#prelude-and-module-index)
- [Foundational Operations](#foundational-operations)
- [Optional and Fallible Values](#optional-and-fallible-values)
- [Arrays, Maps, and Sets](#arrays-maps-and-sets)
- [Ordering, Deques, and Heaps](#ordering-deques-and-heaps)
- [Explicit Iteration](#explicit-iteration)
- [Strings and Unicode](#strings-and-unicode)
- [Numbers and Mathematics](#numbers-and-mathematics)
- [Bytes, Binary Encoding, and Digests](#bytes-binary-encoding-and-digests)
- [Native Strings and Paths](#native-strings-and-paths)
- [Input and Output](#input-and-output)
- [Files and Directories](#files-and-directories)
- [Environment and Processes](#environment-and-processes)
- [Time and Randomness](#time-and-randomness)
- [Execution Boundaries](#execution-boundaries)
- [Testing](#testing)
- [Static Availability](#static-availability)
- [Local Tooling Composition](#local-tooling-composition)
- [Conformance Cases](#conformance-cases)

## Prelude and Module Index

```ril
let values: []int = [1, 2]
let tags: Set<str> = Set::from(["source", "source"])
let found: Option<int> = Array::first(values)
let accepted: Result<(), str> = Ok()
assert(found == Some(1) && len(tags) == 1)
assert(accepted is Ok())
```

Every compilation unit has an enclosing prelude scope. Local declarations may shadow its names; same-scope duplicates are `E0203`. `ril/prelude` re-exports exactly the following declarations.

| Implicit name | Owning module / identity | Contract |
| :--- | :--- | :--- |
| `Option<T>` | `ril/option` | `Some(T)`, `None` |
| `Result<T, E>` | `ril/result` | `Ok(T)`, `Err(E)`; no default E |
| `Immut<T>` | `ril/prelude` | Language-defined immutable qualifier |
| `Options`, `Results` | `ril/option`, `ril/result` | Prelude module aliases |
| `Array`, `Map`, `String` | `ril/array`, `ril/map`, `ril/string` | Module namespaces |
| `Set<T>`, `Set` | `ril/set` | One predefined declaration with type and namespace roles |
| `inner`, `clone`, `clone_immut`, `derive`, `len` | `ril/prelude` | Foundational operations below |
| `panic`, `assert`, `print`, `println` | `ril/prelude` | Defect and output operations below |

`Some`, `None`, `Ok`, and `Err` are available through the visible sum declarations and ordinary constructor abbreviation rules. Re-exporting the same sum does not create another variant candidate. `?T`, `[K: V]`, `[]T`, `[N]T`, primitive type spellings, operators, and the built-in effect identities `Fiber`, `Concurrent`, `Async`, and `Div` belong to the language; they are not extra imports supplied by this table.

```ril
assert(Options::map(Some(2), \x -> x + 1) == Some(3))
let failed: Result<int, str> = Err("bad")
assert(Results::map_err(failed, \message -> len(message)) is Err(3))
```

`Options` and `Results` are prelude aliases of `ril/option` and `ril/result`. They share the original module identities. `Option<T>` and `Result<T, E>` remain type names. Explicit `use` keeps its ordinary namespace derivation; it does not pluralize names.

```ril
-- ril/prelude export excerpt:
pub use ril/option::{Option}
pub use ril/result::{Result}
pub use ril/option as Options
pub use ril/result as Results
```

| Explicit module path | Public surface |
| :--- | :--- |
| `ril/option`, `ril/result` | Prelude types and `Options`/`Results` module identities |
| `ril/array`, `ril/map`, `ril/set`, `ril/string` | Prelude module identities; collection extractors remain qualified/selectively imported |
| `ril/order`, `ril/deque`, `ril/heap`, `ril/iter` | Ordering and additional collections/iteration |
| `ril/unicode`, `ril/string_builder`, `ril/num`, `ril/math` | Text construction, classification, numeric conversion and mathematics |
| `ril/bytes`, `ril/encoding/binary`, `ril/encoding/hex`, `ril/crypto` | Byte data, portable binary encodings, SHA-256 |
| `ril/os`, `ril/path`, `ril/io`, `ril/file` | Native names, paths, streams and filesystem operations |
| `ril/env`, `ril/process`, `ril/time`, `ril/clock`, `ril/random` | Local environment, child processes, clocks and randomness |
| `ril/concurrent`, `ril/concurrent/channel`, `ril/parallel` | Structured execution and communication |
| `ril/test` | Assertion helpers |

All listed modules are part of this version. Network protocols, package acquisition, archive formats, general serialization, regular expressions, and cryptographic primitives other than SHA-256 and system entropy are outside this version's surface.

## Foundational Operations

```ril
type UserId(int)
assert(inner(UserId(1001)) == 1001)
let original = [1, 2, 3]
let mut detached = clone(original)
detached !> Array::push(4)
assert(original == [1, 2, 3] && len(detached) == 4)
let snapshot: Immut<[]int> = clone_immut(detached)
let revised = .{ theme: "dark" } |> derive \mut draft -> {
    draft.theme = "light"
}
assert(revised.theme == "light" && len(snapshot) == 4)
```

| Interface family | Result and governing contract |
| :--- | :--- |
| `inner(wrapper)` | Underlying nominal payload; unit nominal gives `()`; opaque boundary remains sealed |
| `clone(value)` | Isolated ordinary graph; preserve internal aliases/cycles and nested immutable qualifiers |
| `clone_immut(value)` | Independent immutable `Immut<T>` under the same eligibility rules |
| `derive(base, recipe)` | Confined mutable draft; recipe returns `()`; preserve input shape/qualifier and forward recipe effects/outside-state obligations |
| `len(value) -> int` | `str`: Unicode scalars; `bytes`: bytes; arrays/windows: elements; maps/sets: entries |
| `panic(message: str) -> never` | Finite panic initiation, not an algebraic effect |
| `assert(condition: bool, message: str = "assertion failed") -> ()` | False condition panics; ordinary argument evaluation, including message, occurs before the call |
| `print(text: str) -> () @Fiber` | Write UTF-8 to standard output; no added bytes |
| `println(text: str) -> () @Fiber` | Write text followed by one LF byte; no platform newline translation |

`len` is O(n) or better on text and O(1) on the other admitted built-in collections. Copying and derivation cost O(the ordinary graph inspected/copied); no stronger storage-sharing or allocation promise is made. `clone` of a Sender follows the separate [channel resource contract](#structured-concurrency-channels), including `@Fiber`; it is not ordinary-data isolation.

Output convenience functions panic on I/O failure; writes may interleave across tasks. [Fallible output](#input-and-output) returns errors as data. Panic unwinds synchronous frames and runs finite cleanup; cleanup failure during unwinding is a double fault. Assertions do not catch panics.

## Optional and Fallible Values

```ril
-- ril/option
pub type Option<T> { Some(T), None }
pub fn map<T, U>(value: Option<T>, transform: fn(T) -> U) -> Option<U>
pub fn and_then<T, U>(value: Option<T>, transform: fn(T) -> Option<U>) -> Option<U>
pub fn unwrap_or<T>(value: Option<T>, fallback: T) -> T
pub fn unwrap_or_else<T>(value: Option<T>, fallback: fn() -> T) -> T
pub fn expect<T>(value: Option<T>, message: str) -> T

-- ril/result
pub type Result<T, E> { Ok(T), Err(E) }
pub fn map<T, U, E>(value: Result<T, E>, transform: fn(T) -> U) -> Result<U, E>
pub fn map_err<T, E, F>(value: Result<T, E>, transform: fn(E) -> F) -> Result<T, F>
pub fn and_then<T, U, E>(value: Result<T, E>, transform: fn(T) -> Result<U, E>) -> Result<U, E>
pub fn recover<T, E>(value: Result<T, E>, handler: fn(E) -> T) -> T
pub fn expect<T, E>(value: Result<T, E>, message: str) -> T
```

`map`/`and_then` invoke the callback once only on `Some`/`Ok`; `map_err`/`recover` do so only on `Err`. `unwrap_or` evaluates its fallback argument eagerly; `unwrap_or_else` calls it only on `None`. `expect` returns the success payload or panics with the supplied message. Transformations preserve unvisited payloads without copying. Each callback parameter has a separately admitted `mut callback` form, with `&mut`, for invoking a mutable environment; the ordinary form supplies no such authority. These forms do not retain the callback.

All operations are O(1) excluding the invoked callback. They inspect the outer tag. A newly produced `Result`, a returned nested `Result`, or an unvisited nested payload retains its inspection duty under E0720. No `ignore_error` primitive is supplied.

```ril
fn checked_length(raw: Result<str, int>) -> Result<int, str> {
    let text = Results::map_err(raw, \code -> "error {code}")?
    Ok(len(text))
}
assert(checked_length(Ok("abc")) is Ok(3))
-- let _ = checked_length(Err(2))       -- Error [E0720]: wildcard is not inspection
```

## Arrays, Maps, and Sets

### Array

```ril
-- ril/array; Elem accepts []T and [N]T and returns T as a type function.
pub fn first<T>(items: []T) -> ?T
pub fn get<T>(items: []T, index: int) -> ?T
pub fn contains<T>(items: []T, value: T) -> bool
pub fn push<T>(mut items: []T, value: T) &mut
pub fn pop<T>(mut items: []T) -> ?T &mut
pub fn insert<T>(mut items: []T, index: int, value: T) &mut
pub fn remove<T>(mut items: []T, index: int) -> T &mut
pub fn truncate<T>(mut items: []T, length: int) &mut
pub fn reverse<T>(items: []T) -> []T
pub fn concat<T>(left: []T, right: []T) -> []T
pub fn map<T, U>(items: []T, transform: fn(T) -> U) -> []U
pub fn filter<T>(items: []T, predicate: fn(T) -> bool) -> []T
pub fn fold<T, A>(items: []T, initial: A, step: fn(A, T) -> A) -> A
pub fn find<T>(items: []T, predicate: fn(T) -> bool) -> ?T
pub fn any<T>(items: []T, predicate: fn(T) -> bool) -> bool
pub fn all<T>(items: []T, predicate: fn(T) -> bool) -> bool
pub fn for_each<T>(items: []T, action: fn(T) -> ())
```

Read-only Array operations also accept fixed arrays `[N]T` with the same element behavior; length-changing operations require `[]T`. No call grants writes through a slice window. `push` and `insert` additionally admit `^mut value` when retaining an existing writer is requested; that family has `&^mut` and obeys retained sharing. Ordinary insertion preserves only its supplied read permission. All callback operations also admit `mut callback` with `&mut`; both `fold`'s accumulator and returned elements preserve actual provenance.

| Operation | Behavior and complexity |
| :--- | :--- |
| `first`, `get` | `None` if empty/out of bounds, including negative index; O(1) |
| `contains` | Structural equality; stops on first match; O(n) comparisons |
| `push`, `pop` | Append/remove last; empty pop is `None`; amortized O(1) |
| `insert`, `remove` | Insert at `0..=len(items)`, remove at `0..len(items)`; shift later slots; O(n) |
| `truncate` | Negative length panics; length >= current length is a no-op; otherwise remove suffix; O(removed count) |
| `reverse`, `concat` | Fresh outer collection; reverse index order / left then right; O(n) / O(n+m) |
| `map`, `filter` | Fresh outer collection; preserve input order; exactly one callback per element; O(n) |
| `fold` | Strict left fold; empty input returns initial without callback; O(n) |
| `find`, `any`, `all` | Stop at first match / true / false; empty outcomes `None`, false, true; O(n) worst case |
| `for_each` | One invocation per element in order; O(n) |

Active traversal forbids structural mutation of its source through any alias (`E0526`); a still-used live window retains `E0537`. Discarding removed values never discharges uninspected Results. A callback that modifies already visited external state and then panics does not roll back those writes.

```ril
let mut items = [1, 2]
items !> Array::push(3)
assert(Array::filter(items, \x -> x % 2 == 1) == [1, 3])
assert(Array::fold(items, 0, \acc, x -> acc + x) == 6)
assert(Array::get(items, -1) == None)
assert(Array::all([], \x: int -> x > 0))
var seen = 0
let mut count = \x -> { seen += 1; x * 2 }
assert(Array::map(items, mut count) == [2, 4, 6])
assert(seen == 3)
```

### Map

```ril
-- ril/map; Key<[K: V]> = K, Value<[K: V]> = V (type functions).
pub fn get<K, V>(items: [K: V], key: K) -> ?V
pub fn contains<K, V>(items: [K: V], key: K) -> bool
pub fn set<K, V>(mut items: [K: V], key: K, value: V) &mut
pub fn remove<K, V>(mut items: [K: V], key: K) -> ?V &mut
pub fn keys<K, V>(items: [K: V]) -> []K
pub fn values<K, V>(items: [K: V]) -> []V
pub fn entries<K, V>(items: [K: V]) -> [](K, V)
pub fn from<K, V>(entries: [](K, V)) -> [K: V]
```

| Map contract | Rule |
| :--- | :--- |
| Keys | bool, integers including bigint, str, bytes, unit, or nominal/opaque wrappers preserving those value representations |
| Other key types | `E0328`; equality support alone is insufficient |
| `get` / `remove` | None on absence |
| `set` | Insert or replace; preserve existing position; old Result obligations are not discharged |
| `^mut value` | Retain the supplied writer under `&^mut` |
| `keys` / `values` / `entries` | Fresh outer arrays in corresponding insertion order |
| `from` duplicates | Last value, first position; scan left-to-right |
| Values | Preserve provenance; no deep clone |

Key equality is by value. Map equality compares membership, ignoring insertion order. Keys are copied; source reassignment cannot change them. No user equality/hash callback is invoked.

Lookup/update/remove require expected O(1) key operations and O(n) worst case; enumeration/from require O(n) expected key operations. Hash randomization, if any, cannot affect specified order or become a public stable digest.

```ril
let mut settings: [str: int] = ["b": 1, "a": 2]
settings !> Map::set("b", 3)
assert(Map::keys(settings) == ["b", "a"])
assert(Map::remove(mut settings, "b") == Some(3))
settings !> Map::set("b", 4)
assert(Map::keys(settings) == ["a", "b"])
assert(Map::get(settings, "missing") == None)
```

### Set

```ril
-- ril/set; Elem<Set<T>> = T (type function).
pub fn from<T>(items: []T) -> Set<T>
pub fn of<T>(items: []T) -> Set<T>
pub fn contains<T>(items: Set<T>, value: T) -> bool
pub fn insert<T>(mut items: Set<T>, value: T) -> bool &mut
pub fn remove<T>(mut items: Set<T>, value: T) -> bool &mut
pub fn values<T>(items: Set<T>) -> []T
pub fn union<T>(left: Set<T>, right: Set<T>) -> Set<T>
pub fn intersect<T>(left: Set<T>, right: Set<T>) -> Set<T>
pub fn diff<T>(left: Set<T>, right: Set<T>) -> Set<T>
```

| Set operation | Rule |
| :--- | :--- |
| `of` / `from` | Identical; keep first occurrences |
| Elements | Same eligible value types as Map keys; no retained-writer form |
| `insert` / `remove` | True only for a new / previously present member |
| Insert existing / remove then insert | Keep position / append |
| `values` | Insertion order |
| `union` | Left order, then new right members |
| `intersect` / `diff` | Left order |
| Algebra / equality | Fresh outer set / membership equality, ignoring order |
| Complexity | Single-member operations: Map lookup bounds; construction/algebra: expected O(n+m), plus key costs |

```ril
let left = Set::of([3, 1, 3])
let right = Set::from([1, 2])
assert(Set::values(Set::union(left, right)) == [3, 1, 2])
assert(Set::values(Set::intersect(left, right)) == [1])
assert(Set::values(Set::diff(left, right)) == [3])
use ril/array::{Elem}
use ril/map::{Key, Value}
type Element = Elem<[4]u8>
type Name = Key<[str: int]>
type Count = Value<[str: int]>
```

Extractors accept only their listed collection families (`E0301` otherwise); they are type functions, not run-time reflection or collection field projections.

## Ordering, Deques, and Heaps

```ril
-- ril/order
pub type Ordering { Less, Equal, Greater }
pub type Ops<T> = { compare: fn(T, T) -> Ordering }
pub fn sorted<T>(items: []T, ops: Ops<T>) -> []T @{} &{}
pub fn binary_search<T>(items: []T, value: T, ops: Ops<T>) -> Result<int, int> @{} &{}
pub fn compare_int(left: int, right: int) -> Ordering
pub fn compare_str(left: str, right: str) -> Ordering
pub fn compare_bytes(left: bytes, right: bytes) -> Ordering
pub fn total_f64(left: f64, right: f64) -> Ordering
```

| Operation / condition | Rule |
| :--- | :--- |
| `ops.compare` | Explicit, finite, effect/state-free; operands are read-only |
| Comparator relation | Total preorder: reflexive Equal, reversed Less/Greater, transitive comparison and equivalence |
| `sorted` | Fresh outer storage; equal elements retain source order; O(n log n) comparisons |
| Comparison schedule | Unspecified within the stated bound |
| `binary_search` | Sorted input; `Ok(first equal index)` or `Err(lower-bound insertion index)`; O(log n) comparisons |
| Search Result | Must be inspected |
| Inconsistent comparator / unsorted search input | Unspecified result; safety and finite callback bounds still hold |

The first three comparators implement the language's integer/string/byte ordering. `total_f64` orders negative infinity, finite values, positive infinity, then canonical NaN; negative zero precedes positive zero, and NaN compares Equal to NaN. It does not change floating-point `==` or map-key eligibility.

```ril
use ril/order
let order = .{ compare: Order::compare_int }
assert(Order::sorted([3, 1, 1], order) == [1, 1, 3])
assert(Order::binary_search([1, 1, 3], 1, order) is Ok(0))
assert(Order::binary_search([1, 1, 3], 2, order) is Err(2))
type Entry = { rank: int, name: str }
let entries = [Entry.{ rank: 1, name: "a" }, Entry.{ rank: 1, name: "b" }]
let ordered = Order::sorted(entries, .{ compare: \a, b -> Order::compare_int(a.rank, b.rank) })
assert(Array::map(ordered, \.name) == ["a", "b"])
```

```ril
-- ril/deque; Deque<T> is opaque ordinary reference data, not a resource.
pub type Deque<T>
pub fn new<T>() -> Deque<T>
pub fn len<T>(queue: Deque<T>) -> int
pub fn push_front<T>(mut queue: Deque<T>, value: T) &mut
pub fn push_back<T>(mut queue: Deque<T>, value: T) &mut
pub fn pop_front<T>(mut queue: Deque<T>) -> ?T &mut
pub fn pop_back<T>(mut queue: Deque<T>) -> ?T &mut
pub fn values<T>(queue: Deque<T>) -> []T

-- ril/heap; Heap<T> is opaque ordinary reference data.
pub type Heap<T>
pub fn new<T>(ops: Order::Ops<T>) -> Heap<T>
pub fn len<T>(heap: Heap<T>) -> int
pub fn push<T>(mut heap: Heap<T>, value: T) &mut
pub fn peek<T>(heap: Heap<T>) -> ?T
pub fn pop<T>(mut heap: Heap<T>) -> ?T &mut
```

Deque pushes/pops are amortized O(1), length O(1), and `values` O(n), ordered front to back. Empty pops return `None`. Heap creation retains an immutable, environment-free comparator with Order's finite/pure contract; captured mutable/live environments are inadmissible (`E0534`). Heap `peek`/`pop` select the least element; comparator ties select the earliest inserted surviving element. `peek` and length are O(1), push/pop O(log n) comparisons. Heap elements must be immutable ordinary data so comparison keys cannot change through another path; a live element fails immutable publication (`E0535`).

Deque insertions preserve read-only constituent permissions, with no retained-writer form in this version. Heap/Deque receive fresh writable outer storage from `new`; read-only binding does not confer writes. Ordinary clone rules inspect all stored constituents, including the retained comparator. Neither type gets structural projection or a new `for` protocol; use Deque values or explicit pop loops.

## Explicit Iteration

```ril
-- ril/iter: a state transition is an ordinary value, not a suspended continuation.
pub type Step<S, T> { Done, Yielded(T, S) }
pub type Source<S, T> = { step: fn(S) -> Step<S, T> }
pub type Cursor<S> = { mut state: S, mut ended: bool }
pub fn cursor<S>(state: S) -> Cursor<S>
pub fn pull<S, T>(mut cursor: Cursor<S>, source: Source<S, T>) -> ?T &mut
pub fn collect<S, T>(state: S, source: Source<S, T>) -> []T
pub fn fold<S, T, A>(state: S, source: Source<S, T>, initial: A, step: fn(A, T) -> A) -> A
pub fn take<S, T>(source: Source<S, T>, count: int) -> Source<(S, int), T> &capture
pub fn map<S, T, U>(source: Source<S, T>, transform: fn(T) -> U) -> Source<S, U> &capture
pub fn filter<S, T>(source: Source<S, T>, predicate: fn(T) -> bool) -> Source<S, T> &capture
pub fn indexed<T>(items: []T) -> Source<int, T> &capture
```

`cursor` starts with `ended = false`. `pull` calls the source once with the current state: Done sets ended and returns None; Yielded stores the successor and returns Some(item). An ended cursor never calls the source again. If a source aborts, no successor is installed; the source's outside writes are not rolled back. `collect`/`fold` repeat transitions from their supplied initial state until Done. Their returned collection/accumulator follows ordinary provenance rules.

Adapters retain read-only sources/callbacks with their actual provenance and latent obligations.

| Adapter | State and behavior |
| :--- | :--- |
| `map` | Transform each Yielded item once |
| `filter` | Pull until a match or Done; an infinite rejected source may diverge |
| `take(source, count)` | Retain count; state `(source_state, consumed)` starts at `(initial_state, 0)` |
| `take` limit | At count, return Done without pulling; each yielded item increments consumed |
| `take` invalid input | Negative count panics at construction; consumed outside `0..=count` panics before pulling |
| `take` source Done | End immediately |
| `indexed(items)` | State starts at zero; yield increasing indexes until length; negative state panics |
| Retained items | Immutable data or a lawful live view with its stability obligations |

Adapters do not invoke sources or transform callbacks during construction. Pulls forward their actual effects/state; all read-only step/callback handles must be callable with read-only authority. Mutable algorithms can put state in the explicit successor S; this version does not retain a mutable callback handle. `for` gains no user-defined iteration rule. A source retaining an affine `resume` is still `E0611`.

Finite input plus finite callbacks establishes finite traversal. `take` bounds successful items, not time or a diverging source step. `pull` is one source-step cost; adapters add O(1) per inspected item; collect/fold are O(visited transitions). A failing Result item remains subject to inspection even when filtering or terminating early.

```ril
use ril/iter
let source = Iter::indexed([10, 20, 30])
let doubled = Iter::map(source, \x -> x * 2)
let limited = Iter::take(doubled, 2)
assert(Iter::collect((0, 0), limited) == [20, 40])
let mut cursor = Iter::cursor(0)
assert(Iter::pull(mut cursor, source) == Some(10))
```

## Strings and Unicode

### String

```ril
-- ril/string; all positions/counts here are Unicode scalar positions.
pub fn split(text: str, separator: str) -> []str
pub fn trim(text: str) -> str
pub fn contains(text: str, needle: str) -> bool
pub fn starts_with(text: str, prefix: str) -> bool
pub fn ends_with(text: str, suffix: str) -> bool
pub fn replace(text: str, old: str, replacement: str) -> str
pub fn find(text: str, needle: str) -> ?int
pub fn slice(text: str, start: int, end: int) -> ?str
pub fn concat(left: str, right: str) -> str
pub fn join(parts: []str, separator: str) -> str
pub fn lines(text: str) -> []str
pub fn scalar_at(text: str, index: int) -> ?u32
pub fn scalars(text: str) -> []u32
pub fn utf8(text: str) -> bytes
pub fn byte_len(text: str) -> int
pub fn byte_offset(text: str, scalar_index: int) -> ?int
pub fn scalar_offset(text: str, byte_index: int) -> ?int
```

`str` remains immutable valid UTF-8. No function normalizes text implicitly. `find` finds the first exact scalar subsequence; empty needle matches zero. Prefix/suffix/contains accept empty strings. Nonempty-separator split and replace scan non-overlapping occurrences left-to-right; split preserves empty fields including final fields. Empty separator splits into one string per scalar, with no artificial boundary fields; empty text then yields `[]`. Empty `old` inserts replacement at every scalar boundary, including both ends. `slice` accepts `0 <= start <= end <= len(text)`; otherwise None.

`lines` splits at LF, removes a CR immediately preceding each LF, and omits the final empty field caused by a final LF. Empty input gives `[]`; a standalone CR is ordinary text. `trim` removes only the Unicode White_Space property at both ends. `scalar_at` returns None out of bounds. `byte_offset` accepts the end scalar position; `scalar_offset` accepts only exact UTF-8 boundaries including the end. Returned scalars are `u32` values, not a new primitive character type. Byte lengths and offsets are distinct from `len(text)`.

Queries and single scans require O(n*m) or better for n source scalars and m pattern scalars; conversion and construction require O(input+output size). Scalar access/offset conversion may be O(n); repeated scalar indexing has no constant-time guarantee.

```ril
assert(len("Aé🙂") == 3 && String::byte_len("Aé🙂") == 7)
assert(String::byte_offset("Aé🙂", 2) == Some(3))
assert(String::scalar_offset("Aé🙂", 2) == None)
assert(String::scalar_offset("Aé🙂", 7) == Some(3))
assert(String::split("a,,", ",") == ["a", "", ""])
assert(String::split("é🙂", "") == ["é", "🙂"])
assert(String::lines("a\r\nb\n") == ["a", "b"])
assert(String::slice("abc", 2, 1) == None)
assert(String::replace("ab", "", "-") == "-a-b-")
```

### Unicode and StringBuilder

```ril
-- ril/unicode
pub type DecodeError = { offset: int }
pub type ScalarError = { value: u32 }
pub fn decode_utf8(data: bytes) -> Result<str, DecodeError>
pub fn from_scalar(value: u32) -> Result<str, ScalarError>
pub fn is_white_space(value: u32) -> bool
pub fn is_alphabetic(value: u32) -> bool
pub fn is_decimal_digit(value: u32) -> bool
pub fn is_xid_start(value: u32) -> bool
pub fn is_xid_continue(value: u32) -> bool
pub fn lowercase(text: str) -> str
pub fn uppercase(text: str) -> str

-- ril/string_builder; Builder is opaque ordinary mutable reference data.
pub type Builder
pub fn new() -> Builder
pub fn append(mut builder: Builder, text: str) &mut
pub fn append_scalar(mut builder: Builder, value: u32) -> Result<(), Unicode::ScalarError> &mut
pub fn clear(mut builder: Builder) &mut
pub fn to_string(builder: Builder) -> str
```

| Operation / input | Rule |
| :--- | :--- |
| Properties and full case mappings | Unicode 17.0.0; locale-independent |
| XID classification | Text utility; does not change identifier syntax |
| Surrogate / value above U+10FFFF | Scalar construction/appending fails; classifiers return false |
| Case conversion | May expand scalars; no normalization |
| Invalid UTF-8 | Reject overlong forms, surrogates, bad continuation bytes, and truncation; no replacement characters |
| Decode error offset | First byte of the earliest ill-formed subsequence |
| Complexity | Decode/case conversion O(input+output); classification O(1) |

Builder appends are amortized O(appended bytes); clear is O(previous length) or better; to_string is O(length) or better and returns a stable snapshot independent of later appends. Invalid scalar append leaves the builder unchanged. It is not a resource and needs no cleanup.

```ril
use ril/unicode
use ril/string_builder
assert(Unicode::decode_utf8(b"\xC0\xAF") is Err(.{ offset: 0 }))
assert(Unicode::from_scalar(0xD800u32) is Err(_))
let mut builder = StringBuilder::new()
builder !> StringBuilder::append("hello")
let before = StringBuilder::to_string(builder)
builder !> StringBuilder::append("!")
assert(before == "hello" && StringBuilder::to_string(builder) == "hello!")
```

## Numbers and Mathematics

```ril
-- ril/num
pub type NumError { InvalidSyntax, OutOfRange, InvalidRadix }
pub fn parse_int(text: str, radix: int = 10) -> Result<int, NumError>
pub fn parse_bigint(text: str, radix: int = 10) -> Result<bigint, NumError>
pub fn parse_f64(text: str) -> Result<f64, NumError>
pub fn format_int(value: int, radix: int = 10) -> Result<str, NumError>
pub fn format_bigint(value: bigint, radix: int = 10) -> Result<str, NumError>
pub fn format_f64(value: f64) -> str
pub fn convert<T, U>(value: T) -> Result<U, NumError>
```

The same signatures export `parse_i8/i16/i32/i64/u8/u16/u32/u64/f32` and `format_*` for their named types. `int` uses the target's pointer-sized range.

| Integer conversion | Rule |
| :--- | :--- |
| Input | Whole string; locale-independent; no whitespace, underscores, or prefix |
| Radix | 2..36; InvalidRadix is checked first |
| Digits | Optional sign, then at least one ASCII digit; a..z is case-insensitive |
| Negative unsigned input | OutOfRange unless magnitude is zero |
| Output | Lowercase digits; minus for negatives only; no padding/prefix |

| Floating conversion | Rule |
| :--- | :--- |
| Decimal input | `[sign] digits ['.' digits] [exponent]` or `[sign] '.' digits [exponent]` |
| Exponent | e/E, optional sign, one or more digits |
| Special input | Exact tokens `nan`, `inf`, `+inf`, `-inf` |
| Rounding | Once, nearest ties-to-even; finite overflow is OutOfRange; underflow may yield signed zero |
| Finite output | Shortest round-tripping decimal; among ties choose the closest value, then even final digit |
| Notation | Fixed for decimal exponents -6..20, scientific otherwise |
| Zero / specials | `-0.0` preserves negative zero; `nan`, `inf`, `-inf` |
| Fixed integer-like output | Include `.0` |
| Scientific exponent | No leading zero or positive sign |

`convert<T,U>` accepts numeric T/U only. Integer-to-integer conversion must fit; float-to-integer requires finite, integral, representable input; integer/float-to-float rounds once and rejects finite overflow. NaN converts only between floats and canonicalizes; infinities convert only between floats. No conversion is implicit. Numeric parsing/formatting is finite; bigint work includes operand digit counts, with O(d²) or better arithmetic work for d digits.

```ril
use ril/num
assert(Num::parse_int("ff", 16) is Ok(255))
assert(Num::parse_u8("256") is Err(Num::NumError::OutOfRange))
assert(Num::parse_int(" 1") is Err(Num::NumError::InvalidSyntax))
assert(Num::convert<f64, int>(1.5) is Err(Num::NumError::OutOfRange))
assert(Num::parse_bigint("18446744073709551616") is Ok(_))
```

```ril
-- ril/math; f32 variants use the suffix _f32.
pub let PI: f64
pub let TAU: f64
pub fn sqrt(value: f64) -> f64
pub fn floor(value: f64) -> f64
pub fn ceil(value: f64) -> f64
pub fn round(value: f64) -> f64
pub fn abs(value: f64) -> f64
pub fn is_nan(value: f64) -> bool
pub fn is_finite(value: f64) -> bool
pub fn min(left: f64, right: f64) -> f64
pub fn max(left: f64, right: f64) -> f64
```

All listed operations are finite.

| Operation | Rule |
| :--- | :--- |
| `sqrt` | Correctly rounded, nearest ties-to-even; negative nonzero gives canonical NaN; preserve negative zero |
| `round` | Nearest integral float, ties-to-even |
| `floor` / `ceil` | Integral rounding toward negative / positive infinity |
| Integral rounding | Preserve signed zero; pass through infinity/NaN |
| `abs` | Clear sign |
| `min` / `max` | NaN input gives canonical NaN; zero tie selects negative / positive zero |
| PI / TAU | Nearest f64 to pi / 2*pi, independent of host math modes |
| PI_F32 / TAU_F32 | Round directly to f32 |

Transcendental approximations are not exported.

## Bytes, Binary Encoding, and Digests

```ril
-- ril/bytes
pub fn from_array(items: []u8) -> bytes
pub fn to_array(data: bytes) -> []u8
pub fn slice(data: bytes, start: int, end: int) -> ?bytes
pub fn concat(left: bytes, right: bytes) -> bytes
pub fn find(data: bytes, needle: bytes) -> ?int
pub fn at(data: bytes, index: int) -> ?u8
```

`bytes` is immutable value data. `from_array` snapshots bytes; `to_array` produces fresh writable outer storage. Later array mutation cannot affect the byte value. Slice uses half-open byte offsets and returns None on invalid bounds. Find returns the first byte offset; empty needle returns Some(0). At returns None out of bounds. Copy/concat is O(input+output), at O(1), slice O(selected length) or better, find O(n*m) or better. No encoding is implied.

```ril
-- ril/encoding/binary
pub type ByteOrder { Little, Big }
pub type BinaryError { UnexpectedEnd, Overflow, NonCanonical }
pub type Cursor = { data: bytes, mut offset: int }
pub fn cursor(data: bytes) -> Cursor
pub fn remaining(cursor: Cursor) -> int
pub fn read_u8(mut cursor: Cursor) -> Result<u8, BinaryError> &mut
pub fn read_u32(mut cursor: Cursor, order: ByteOrder) -> Result<u32, BinaryError> &mut
pub fn read_u64(mut cursor: Cursor, order: ByteOrder) -> Result<u64, BinaryError> &mut
pub fn read_bytes(mut cursor: Cursor, count: int) -> Result<bytes, BinaryError> &mut
pub fn read_uleb128(mut cursor: Cursor) -> Result<u64, BinaryError> &mut
pub fn write_u8(mut output: []u8, value: u8) &mut
pub fn write_u32(mut output: []u8, value: u32, order: ByteOrder) &mut
pub fn write_u64(mut output: []u8, value: u64, order: ByteOrder) &mut
pub fn write_bytes(mut output: []u8, value: bytes) &mut
pub fn write_uleb128(mut output: []u8, value: u64) &mut
```

Fixed-width read/write families also export `i8`, `i16`, `u16`, `i32`, `i64`, `f32`, `f64` suffixes with corresponding value types. Eight-bit functions omit `order`. Integers use their two's-complement bit representation; floats use IEEE bits with canonical NaN on both reading and writing. ByteOrder controls low-to-high versus high-to-low byte significance, independent of the target. Pointer-sized `int` is never serialized implicitly. All writers append; they do not expose spare capacity.

| Cursor / encoding condition | Outcome |
| :--- | :--- |
| New cursor | Offset zero |
| Offset outside `0..=len(data)` / negative count | Panic before access |
| Successful read | Advance by bytes consumed |
| Any Err | Preserve offset |
| Short input | UnexpectedEnd |
| ULEB128 byte | Low seven bits are payload; bit 7 means continuation |
| ULEB128 output | Shortest u64 encoding; zero is one zero byte |
| More than 64 payload bits / invalid or continuing tenth byte | Overflow; inspect at most ten bytes |
| Redundant terminating high zero group | NonCanonical |
| Missing bytes before overflow is established | UnexpectedEnd |
| Complexity | Fixed width O(width); bytes O(count); ULEB128 O(10) |

```ril
use ril/bytes
use ril/encoding/binary
let mut output: []u8 = []
output !> Binary::write_u32(0x01020304u32, Binary::ByteOrder::Little)
output !> Binary::write_uleb128(128u64)
let frozen = Bytes::from_array(output)
assert(frozen == b"\x04\x03\x02\x01\x80\x01")
let mut cursor = Binary::cursor(frozen)
assert(Binary::read_u32(mut cursor, Binary::ByteOrder::Little) is Ok(0x01020304u32))
assert(Binary::read_uleb128(mut cursor) is Ok(128u64))
assert(Binary::read_u8(mut cursor) is Err(Binary::BinaryError::UnexpectedEnd))
assert(cursor.offset == 6)
let mut bad = Binary::cursor(b"\x80\x00")
assert(Binary::read_uleb128(mut bad) is Err(Binary::BinaryError::NonCanonical))
assert(bad.offset == 0)
```

```ril
-- ril/encoding/hex
pub type HexError = { offset: int }
pub fn encode(data: bytes) -> str
pub fn decode(text: str) -> Result<bytes, HexError>

-- ril/crypto
pub fn sha256(text: str) -> bytes
pub fn sha256_bytes(data: bytes) -> bytes
```

| Operation | Contract |
| :--- | :--- |
| Hex encode | Two lowercase ASCII digits per byte; O(n) |
| Hex decode | Either case; no prefix/whitespace; O(n) |
| Invalid hex scalar | Report its scalar index |
| Otherwise valid odd-length hex | Report the final unpaired digit's index |
| SHA-256 | Exactly 32 digest bytes; identical across platforms; O(input length) |
| `sha256(text)` | Hash `String::utf8(text)` |
| Excess SHA-256 input length | Panic |

Digest functions accept only the displayed text/byte inputs; they perform no structural serialization.

```ril
use ril/crypto
use ril/encoding/hex
assert(Hex::encode(Crypto::sha256("abc")) ==
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
assert(Hex::decode("0A") is Ok(b"\x0A"))
assert(Hex::decode("0") is Err(.{ offset: 0 }))
```

## Native Strings and Paths

```ril
-- ril/os; NativeString is opaque ordinary immutable value data.
pub type NativeString
pub type NativeError { InvalidEncoding, WrongPlatform }
pub type Platform { Windows, Posix }
pub fn platform() -> Platform
pub fn from_string(text: str) -> NativeString
pub fn to_string(value: NativeString) -> Result<str, NativeError>
pub fn from_posix_bytes(data: bytes) -> Result<NativeString, NativeError>
pub fn posix_bytes(value: NativeString) -> Result<bytes, NativeError>
pub fn from_windows_units(units: []u16) -> Result<NativeString, NativeError>
pub fn windows_units(value: NativeString) -> Result<[]u16, NativeError>
pub fn compare(left: NativeString, right: NativeString) -> Order::Ordering
```

| Native-string operation | Rule |
| :--- | :--- |
| `platform` | Target-fixed Windows or Posix (Linux/macOS); finite and effect-free |
| Representation | Arbitrary POSIX bytes / Windows UTF-16 units; preserve ill-formed Unicode |
| Wrong-platform constructor/extractor | WrongPlatform |
| Conversion to/from `str` | UTF-8 on POSIX, UTF-16 on Windows; strict InvalidEncoding on failure; no normalization |
| NUL | Preserved in NativeString; rejected at an OS name/argument boundary |
| Windows unit extraction | Immutable snapshot |
| Equality / keys | Native value equality; no filesystem lookup |
| `compare` | Case-sensitive lexicographic unsigned-unit order |
| Complexity | Conversion O(n); comparison O(common prefix) |

```ril
-- ril/path; Path is opaque ordinary immutable value data over a NativeString.
pub type Path
pub fn from_string(text: str) -> Path
pub fn from_native(value: Os::NativeString) -> Path
pub fn native(path: Path) -> Os::NativeString
pub fn to_string(path: Path) -> Result<str, Os::NativeError>
pub fn join(base: Path, child: Path) -> Path
pub fn parent(path: Path) -> ?Path
pub fn file_name(path: Path) -> ?Os::NativeString
pub fn extension(path: Path) -> ?Os::NativeString
pub fn is_absolute(path: Path) -> bool
pub fn normalize_lexical(path: Path) -> Path
pub fn compare(left: Path, right: Path) -> Order::Ordering
```

Path equality/compare preserve the exact native spelling, including separator spelling and case; equivalent spellings may refer to one file without comparing equal. Paths are admissible map keys as value wrappers. Constructors perform no existence check or normalization. Every operation in this section is finite, has no environmental effects, and is O(path length) or better.

| Rule | POSIX | Windows |
| :--- | :--- | :--- |
| Separators | `/` only; backslash is ordinary data | Both `/` and `\` in ordinary paths |
| Absolute path | Begins with `/` | Drive plus rooted separator, or UNC server/share root |
| Relative drive | No drive syntax | `C:part` is drive-relative, not absolute |
| Join with absolute child | Replace base | Replace base |
| Join with rooted child lacking drive | Replace base | Retain base drive/UNC share root; replace components |
| Join with drive-relative child | Ordinary component | Replace base with that drive-relative child; do not consult per-drive current directories |
| Case and normalization | No case folding or Unicode normalization | No case folding or Unicode normalization |

Otherwise join inserts one native separator if needed; an empty base returns the child, and an empty child leaves the base unchanged. Parent/file_name ignore trailing separators, preserve the root, and treat `.`/`..` as lexical components. A root/empty path has no file_name or parent; a single relative component has parent `Some(empty path)`. Extension is the suffix after the final dot in file_name, excluding a leading dot alone: `.profile` has None, `a.` has Some(empty), `a.tar.gz` has `gz`.

`normalize_lexical` removes `.` and redundant separators, cancels a normal component followed by `..`, preserves leading `..` on relative paths, and never climbs above an absolute root. It emits native separators and `.` for an empty relative result. It does not resolve symlinks and need not preserve filesystem meaning in their presence. Windows verbatim/device prefixes (`\\?\`, `\\.\`) are preserved exactly by lexical operations; join appends a child only when it is relative and has no prefix, using `\`, and normalization returns these paths unchanged. Native filesystem operations still validate supported names.

```ril
use ril/os
use ril/path
let path = Path::from_string("src/main.ril")
assert(Path::extension(path) == Some(Os::from_string("ril")))
assert(Path::file_name(Path::from_string(".profile")) == Some(Os::from_string(".profile")))
assert(Path::extension(Path::from_string(".profile")) == None)
if Os::platform() == Os::Platform::Posix {
    let raw = Os::from_posix_bytes(b"a\xFF") ?? \_error -> panic("wrong platform")
    assert(Os::to_string(raw) is Err(Os::NativeError::InvalidEncoding))
    assert(Os::posix_bytes(raw) is Ok(b"a\xFF"))
}
```

## Input and Output

### Error and Stream Contracts

```ril
-- ril/io
pub type ErrorKind {
    NotFound, PermissionDenied, AlreadyExists, InvalidInput, InvalidData,
    UnexpectedEnd, BrokenPipe, Closed, Unsupported, Other,
}
pub type IoError = { kind: ErrorKind, message: str, native_code: ?i64 }
pub type ReadChunk = { data: bytes, end: bool }
pub type WriteProgress = { written: int, error: ?IoError }
pub type ReadOps<R> = { read: fn(mut R, int) -> Result<ReadChunk, IoError> &mut }
pub type WriteOps<W> = { write: fn(mut W, bytes) -> WriteProgress &mut }
pub fn read_all<R>(mut reader: R, ops: ReadOps<R>) -> Result<bytes, IoError> &mut
pub fn write_all<W>(mut writer: W, data: bytes, ops: WriteOps<W>) -> Result<(), IoError> &mut
pub fn stdin_read(max_bytes: int) -> Result<ReadChunk, IoError> @Fiber
pub fn stdout_write(data: bytes) -> WriteProgress @Fiber
pub fn stderr_write(data: bytes) -> WriteProgress @Fiber
pub fn write_stdout(text: str) -> Result<(), IoError> @Fiber
pub fn write_stderr(text: str) -> Result<(), IoError> @Fiber
pub fn error_text(error: IoError) -> str
```

Operation records receive the caller's explicit mutable data handle. Their actual effect and state obligations are forwarded; a memory source need not have `@Fiber`, while a file source does. These records are ordinary Ril values, not implicit interface instances. Stream helpers do not retain a receiver or operation record after the call. Their excluded/covered computation and termination judgments depend on the selected operations.

For a positive `max_bytes`, successful read returns at most that many bytes, with nonempty data or `end = true`. `end` means EOF after these bytes; it may accompany the last nonempty chunk. A zero request on a valid open stream returns empty data with `end = false`, without waiting or consuming; handle/mode validation still applies. A negative request panics. A read that obtained bytes before encountering an error returns those bytes first and reports the error on the next positive request; `Err` never silently consumes unreported data. EOF is an ordinary success, not IoError. Invalid UTF-8 is a text-decoding failure, not a byte-read failure.

| Operation / result | Rule |
| :--- | :--- |
| WriteProgress | `0 <= written <= len(data)`; progress and error may coexist |
| Written prefix | Committed; retry only the remaining suffix |
| Nonempty input, zero written, no error | Contract violation |
| Empty write | Validate handle/mode, then return zero without error |
| `write_all` | Retry the suffix until completion or first error; no rollback |
| `write_stdout` / `write_stderr` | UTF-8, write-all behavior |
| `read_all` | Accumulate until EOF; error returns Err without accumulated data or position rollback |

All OS interaction has `@Fiber`; waiting operations are cancellation points. Structured cancellation abandons the wait under the language rules, never fabricating EOF, an empty successful write, or an IoError. No wall-clock completion guarantee is made. The caller must process WriteProgress.error: it is an Option, so it has no automatic Result inspection obligation; `write_all` is the checked convenience interface.

IoError.kind is portable. Message spelling, native-code presence and numeric values are explanatory/platform-specific. `error_text` returns message and is pure. OS errors without a portable classification map to Other. Invalid encodings map to InvalidData, invalid names/arguments to InvalidInput, and unavailable operations to Unsupported. Helpers perform O(transferred bytes) work plus selected operation costs.

### Buffered Streams

```ril
-- ril/io; these are ordinary in-memory state, not owning resources.
pub type ReadBuffer
pub type WriteBuffer
pub fn read_buffer(capacity: int) -> ReadBuffer
pub fn write_buffer(capacity: int) -> WriteBuffer
pub fn read_buffered<R>(mut buffer: ReadBuffer, mut reader: R,
    ops: ReadOps<R>, max_bytes: int) -> Result<ReadChunk, IoError> &mut
pub fn write_buffered<W>(mut buffer: WriteBuffer, mut writer: W,
    ops: WriteOps<W>, data: bytes) -> WriteProgress &mut
pub fn flush<W>(mut buffer: WriteBuffer, mut writer: W,
    ops: WriteOps<W>) -> Result<(), IoError> &mut
```

| Buffered operation | Rule |
| :--- | :--- |
| Capacity <= 0 | Panic before receiver access |
| Read ahead | At most capacity; preserve stream byte/EOF/error behavior |
| Unread data or deferred error | No direct-read interleaving or switching readers |
| WriteProgress.written | Bytes accepted from this call, including buffered bytes |
| Flush | Send in order; remove confirmed prefixes; preserve the unwritten suffix after error |
| Pending output | Switching destinations is a contract violation |
| Mutable arguments | Buffer and receiver must be disjoint |
| Bookkeeping | Finite O(bytes), excluding waits |

Buffers never retain resource authority or auto-flush on scope exit. Discarding a nonempty write buffer abandons its bytes; callers requiring delivery must explicitly inspect flush. Stream closure does not imply a successful flush. Writing bytes and ensuring durable filesystem storage are separate operations.

```ril
use ril/io
use ril/bytes
type Sink = { mut data: []u8 }
fn partial_write(mut sink: Sink, data: bytes) -> Io::WriteProgress &mut {
    if len(data) == 0 { return .{ written: 0, error: None } }
    let count = if len(data) >= 2 { 2 } else { len(data) }
    for 0..count as index {
        let byte_value = Bytes::at(data, index) ?? panic("invalid fixture index")
        sink.data !> Array::push(byte_value)
    }
    .{ written: count, error: Some(.{
        kind: Io::ErrorKind::BrokenPipe, message: "closed", native_code: None,
    }) }
}
pub fn test_partial_output() {
    let mut sink = Sink.{ data: [] }
    let result = Io::write_all(mut sink, b"abcd", .{ write: partial_write })
    match result {
        Err(error) -> assert(error.kind == Io::ErrorKind::BrokenPipe),
        Ok() -> panic("expected a write error"),
    }
    assert(Bytes::from_array(sink.data) == b"ab") -- No duplicate prefix or rollback
}
```

## Files and Directories

```ril
-- ril/file
pub type Handle
pub type OpenMode { Read, WriteNew, WriteTruncate, ReadWrite, Append }
pub type SeekFrom { Start(i64), Current(i64), End(i64) }
pub type FileKind { Regular, Directory, Symlink, Other }
pub type Metadata = { kind: FileKind, size: u64, modified: ?Time::Timestamp }
pub type Entry = { path: Path::Path, name: Os::NativeString, kind: FileKind }
pub fn open(path: str) -> Result<Handle, Io::IoError> @Fiber
pub fn read(path: str) -> Result<str, str> @Fiber
pub fn open_path(path: Path::Path, mode: OpenMode) -> Result<Handle, Io::IoError> @Fiber
pub fn read_chunk(mut file: Handle, max_bytes: int) -> Result<Io::ReadChunk, Io::IoError> @Fiber &mut
pub fn write(mut file: Handle, data: bytes) -> Io::WriteProgress @Fiber &mut
pub fn seek(mut file: Handle, position: SeekFrom) -> Result<u64, Io::IoError> @Fiber &mut
pub fn sync(mut file: Handle) -> Result<(), Io::IoError> @Fiber &mut
pub fn close(mut file: Handle) -> Result<(), Io::IoError> @Fiber &mut
pub fn read_bytes(path: Path::Path) -> Result<bytes, Io::IoError> @Fiber
pub fn read_text(path: Path::Path) -> Result<str, Io::IoError> @Fiber
pub fn write_bytes(path: Path::Path, data: bytes) -> Result<(), Io::IoError> @Fiber
pub fn write_text(path: Path::Path, text: str) -> Result<(), Io::IoError> @Fiber
pub fn metadata(path: Path::Path, follow_links: bool = true) -> Result<Metadata, Io::IoError> @Fiber
pub fn read_dir(path: Path::Path) -> Result<[]Entry, Io::IoError> @Fiber
pub fn create_dir(path: Path::Path) -> Result<(), Io::IoError> @Fiber
pub fn create_dir_all(path: Path::Path) -> Result<(), Io::IoError> @Fiber
pub fn remove_file(path: Path::Path) -> Result<(), Io::IoError> @Fiber
pub fn remove_dir(path: Path::Path) -> Result<(), Io::IoError> @Fiber
pub fn rename(source: Path::Path, destination: Path::Path) -> Result<(), Io::IoError> @Fiber
pub fn canonicalize(path: Path::Path) -> Result<Path::Path, Io::IoError> @Fiber
pub fn temp_file(directory: Path::Path) -> Result<(Path::Path, Handle), Io::IoError> @Fiber
pub fn with_file<T>(path: Path::Path, mode: OpenMode,
    action: fn(mut Handle) -> Result<T, Io::IoError>) -> Result<T, Io::IoError> @Fiber
```

The existing `File::read(path: str)` reads UTF-8 text and maps IoError through error_text. `open(str)` is `open_path(Path::from_string(path), Read)`. Handle streaming uses `read_chunk`, with no overloaded whole-file/stream name. `File` is explicitly imported; it is not in the prelude.

| OpenMode | Required behavior |
| :--- | :--- |
| Read | Existing file, reading only |
| WriteNew | Exclusive creation; existing path is AlreadyExists |
| WriteTruncate | Create if absent; truncate existing regular file |
| ReadWrite | Existing file, reads and writes, no truncation |
| Append | Create if absent; each write appends at the then-current end; no cross-call atomicity promise |

Handle is a task-local opaque resource with external position/open state. `open`, `open_path`, and temp_file grant a fresh operation authority that may enter `let scoped mut`. Cloning, immutable copying, derivation, child capture, and transfer have no file-resource exemption (`E0530`, `E0536`, `E0601`, or `E0908` as applicable). A plain read-only alias cannot perform mutable operations. All aliases observe closure; operations after close return Err(Closed) without touching the file. Repeated close succeeds as a no-op.

| File cleanup | Contract |
| :--- | :--- |
| `let scoped mut` exit | Release once; finite, non-suspending, no residual effect or panic |
| Implicit release | Abandon descriptor; report no host error; perform no flush/sync |
| Explicit `close` | Mark closed before reporting an error; suppress later release |
| `on_close` callbacks | Still require finite computation and no residual effects |
| Unregistered handle | Explicit close required; GC gives no timely-close guarantee |

Implicit release is a separate operation from effectful `close`.

`with_file` opens, invokes action once with a temporary writable Handle, and closes before returning. It forwards actual callback effects/state; the borrowed handle and its aliases cannot escape (`E0604`). If action returns Err, that error takes precedence over a close error; on Ok, a close error replaces success. On abnormal unwinding, perform the finite release action without replacing the original cause. The wrapper does not use an effectful scoped destructor.

Read_chunk/write obey Io progress rules and change the handle's position by transferred bytes. An operation unsupported by the handle's OpenMode returns InvalidInput without accessing data; an underlying host access denial is PermissionDenied. Seek computes a nonnegative representable offset; otherwise InvalidInput, without changing position. Non-seekable resources report Unsupported. Seeking beyond EOF does not itself extend a file. `sync` requests that prior file writes reach the host's stable-storage boundary; it does not sync an enclosing directory or promise crash-atomic replacement.

Whole-file reads/writes close their internal handle on all exits; writes use WriteTruncate and write-all behavior. They are not atomic replacement and may leave a written prefix on error. Text uses strict UTF-8 with no BOM stripping or newline translation. Read_text maps an invalid encoding to InvalidData. Metadata.size counts bytes for regular files; other kinds have size zero. Missing timestamp precision is represented by the supplied timestamp's documented precision, or None if unavailable. Metadata follows links by default; false reports the link itself.

| Filesystem operation | Contract |
| :--- | :--- |
| `read_dir` | Immediate children except `.`/`..`; sort native names with `Os::compare` |
| Enumeration consistency | Snapshot names/kinds, no transaction; disappearance may fail; Err returns no partial array |
| `create_dir` / `create_dir_all` | Existing path fails / existing directories accepted |
| `remove_file` | Remove the file or link itself |
| `remove_dir` | Empty directory only; no recursion |
| `rename` | Existing destination: AlreadyExists; cross-filesystem move: Unsupported |
| `canonicalize` | Query existing objects, resolve links, return absolute native path |
| Unsupported/unrepresentable path | InvalidInput/Unsupported; no lossy conversion |

Temp_file exclusively creates a new empty file in the given existing directory, returns its path and writable Handle, and does not delete the path on close. The filename spelling is unspecified; creation must not reuse an existing file. Cleanup of the directory entry is explicit. No helper silently deletes directory trees.

```ril
use ril/file
use ril/path
use ril/io
pub fn copy_text(source: Path::Path, destination: Path::Path) -> Result<(), Io::IoError> @Fiber {
    let text = File::read_text(source)?
    File::write_text(destination, text)
}
pub fn read_prefix(path: str) -> Result<bytes, Io::IoError> @Fiber {
    let scoped mut file = File::open(path)?
    let chunk = File::read_chunk(mut file, 4)?
    File::close(mut file)?
    Ok(chunk.data)
}
```

## Environment and Processes

```ril
-- ril/env
pub fn args() -> []Os::NativeString @Fiber
pub fn get(name: Os::NativeString) -> Result<?Os::NativeString, Io::IoError> @Fiber
pub fn all() -> [](Os::NativeString, Os::NativeString) @Fiber
pub fn current_dir() -> Result<Path::Path, Io::IoError> @Fiber
pub fn temp_dir() -> Result<Path::Path, Io::IoError> @Fiber
```

| Environment data | Rule |
| :--- | :--- |
| `args` | Immutable snapshot excluding program name; POSIX preserves native bytes; Windows uses the argument rules below |
| `get` | Absent: None; present empty value: Some(empty) |
| Name validation | Nonempty, host-representable, no NUL or `=`; otherwise InvalidInput |
| Name equality | POSIX case-sensitive; Windows ordinal case-insensitive |
| `all` | One entry per effective name, sorted by native-name comparison |
| Hidden entries | Empty names and Windows `=`-prefixed drive-directory pseudo-variables |
| Values | Native strings; no implicit Unicode decoding |

These calls observe the environment at invocation and do not promise a transaction across calls. Current_dir returns an absolute native path. Temp_dir returns the host's selected absolute temporary directory, without creating it or guaranteeing writability. This version exposes no global environment/current-directory mutation; child-specific overrides are explicit process inputs.

```ril
-- ril/process
pub type Input { Inherit, Null, Data(bytes) }
pub type OutputMode { Inherit, Null, Capture }
pub type Command = {
    program: Path::Path,
    args: []Os::NativeString,
    cwd: ?Path::Path,
    env: ?[](Os::NativeString, Os::NativeString),
    input: Input,
    stdout: OutputMode,
    stderr: OutputMode,
}
pub type ExitStatus { Exited(u32), Signaled(int) }
pub type Output = { status: ExitStatus, stdout: bytes, stderr: bytes }
pub type ProcessError {
    InvalidCommand(str), StartFailed(Io::IoError), WaitFailed(Io::IoError),
    CaptureLimit, TransferFailed(Io::IoError),
}
pub type Child
pub fn command(program: Path::Path, args: []Os::NativeString) -> Command
pub fn run(command: Command, capture_limit: int = 16777216) -> Result<Output, ProcessError> @Fiber
pub fn spawn(command: Command) -> Result<Child, ProcessError> @Fiber
pub fn wait(mut child: Child) -> Result<ExitStatus, ProcessError> @Fiber &mut
pub fn terminate(mut child: Child) -> Result<(), ProcessError> @Fiber &mut
pub fn with_child<T>(command: Command,
    action: fn(mut Child) -> Result<T, ProcessError>) -> Result<T, ProcessError> @Fiber
pub fn success(status: ExitStatus) -> bool
```

| Command field | Rule |
| :--- | :--- |
| Defaults | `cwd = None`, `env = None`, inherited streams; construction is effect-free |
| Program | Explicit path; no PATH search, file association, shell expansion, globbing, or string splitting |
| Relative program/cwd | Resolve against caller directory at invocation, before applying child cwd |
| Env None / Some(entries) | Snapshot inherited environment / replace completely |
| Invalid command | NUL in program/argument/environment, invalid environment name, or duplicate effective name: InvalidCommand before launch |
| Child overrides | Leave parent environment/directory unchanged |

| Argument encoding | Rule |
| :--- | :--- |
| POSIX | Native argv elements; program supplied separately as argv[0] |
| Windows | Quote every argument; double backslashes before a quote, then escape the quote; double trailing backslashes before the closing quote |
| Other Windows backslashes | Preserve unchanged |
| Windows child parsing | Empty/space arguments round-trip under these quoting rules; another parser may interpret them differently |
| Windows `Env::args` | Apply the inverse rules; omit executable-name element |
| Shell syntax/scripts | Pass an explicit shell executable and argument vector |

| `run` event | Outcome |
| :--- | :--- |
| Invocation | Start one process; supply Data input while draining captures; wait for exit; `@Fiber` |
| Noncaptured stream | Empty bytes in Output |
| Capture limit | Combined stdout/stderr bytes; negative limit panics before launch |
| Limit exceeded | Terminate/reap child; CaptureLimit; no partial Output |
| Transfer failure | Terminate/reap child; TransferFailed; prior external writes remain committed |
| Captured ordering | Preserve each stream's order; no merged order |
| Nonzero exit | `Ok(Output)` containing Exited(nonzero) |
| Signaled | POSIX only; Windows returns its unsigned exit code |

Spawn accepts only Inherit/Null for all streams; Data/Capture is InvalidCommand. It returns a task-local opaque Child with fresh wait/terminate authority. Child is not ordinary data, not clonable/derivable/transferable, and has **no** `let scoped` cleanup contract (`E0541`). Wait caches the observed status so repeated waits return it. Terminate requests forced termination of this child and then waits for/reaps it; an already exited child succeeds. It does not promise to kill arbitrary descendants started by that external process. A failed termination returns WaitFailed without pretending the process was reaped.

| Process ownership / exit | Rule |
| :--- | :--- |
| `with_child` action | Invoke once with a nonescaping temporary Child |
| Wrapper exit | Terminate/wait for a running child; reap a completed child |
| Action Ok / Err | Return cleanup failure / preserve action error |
| Panic, cancellation, abort | Complete required child cleanup before propagating; no wall-clock bound |
| Cancel `run` or owning `with_child` | Cancel transfers, terminate/reap, continue non-resumable cancellation |
| Standalone spawn | Explicit wait/terminate required; aliases and GC do not ensure cleanup |
| Cancel `wait` | Cleanup authority remains with the owner |

`with_child` is effectful. Child has no `on_close` contract.

Success is true only for Exited(0), and is pure. Command construction is O(argument/environment size); output processing is O(transferred bytes), excluding external execution and waits. None of these waits establishes finite pure computation or eligibility for Div budgets.

```ril
use ril/process
use ril/path
use ril/os
-- The fixture supplies an executable path; no shell parsing is requested.
let command = Process::command(executable_path, [Os::from_string("a b"), Os::from_string("")])
let captured = command |> derive \mut draft -> {
    draft.stdout = Process::OutputMode::Capture
    draft.stderr = Process::OutputMode::Capture
}
let output = Process::run(captured) ?? \_error -> panic("process operation failed")
let was_successful = Process::success(output.status)
-- A child that exits 7 produces Ok({status: Exited(7), ...}); was_successful is false.
```

## Time and Randomness

```ril
-- ril/time
pub type Duration(i64)
pub type Timestamp = { seconds: i64, nanos: u32 }
pub type Instant
pub type TimeError { OutOfRange, DifferentClock }
pub fn duration_nanos(value: i64) -> Duration
pub fn timestamp(seconds: i64, nanos: u32) -> Result<Timestamp, TimeError>
pub fn add(value: Timestamp, duration: Duration) -> Result<Timestamp, TimeError>
pub fn elapsed(start: Instant, end: Instant) -> Result<Duration, TimeError>
pub fn monotonic() -> Instant @Fiber
pub fn sleep(duration: Duration) -> () @Fiber

-- ril/clock
pub fn now() -> Time::Timestamp @Fiber

-- ril/random; Rng is opaque ordinary mutable reference data.
pub type Rng
pub fn seeded(seed: u64) -> Rng
pub fn next_u64(mut rng: Rng) -> u64 &mut
pub fn below(mut rng: Rng, upper: u64) -> u64 &mut
pub fn entropy(count: int) -> Result<bytes, Io::IoError> @Fiber
```

| Time value / operation | Rule |
| :--- | :--- |
| Duration | Signed nanoseconds |
| Timestamp | POSIX seconds from 1970-01-01T00:00:00Z, excluding leap seconds; nanos in `0..1_000_000_000` |
| Invalid timestamp construction or input | OutOfRange |
| `add` | Exact arithmetic, normalize; unrepresentable result: OutOfRange |
| `Clock::now` | Normalized timestamp; round sub-nanosecond precision down; unavailable finer digits are zero |
| Wall time | May decrease |
| Clock observation failure | Boundary panic; no fabricated value |

| Monotonic operation | Rule |
| :--- | :--- |
| Instant | Opaque ordinary immutable value with clock domain; no wall-time conversion/serialization |
| `elapsed` | Different domains: DifferentClock; negative/unrepresentable difference: OutOfRange |
| Observations in one domain | Nondecreasing; equal values allowed |
| `sleep` negative / zero | Panic before waiting / return immediately |
| Positive sleep | Complete no earlier than the requested monotonic duration |
| Cancellation | Non-resumable exit; never successful early completion |
| Arithmetic / observations | Finite O(1) / `@Fiber`, run-time only |

Seeded generation uses this exact 64-bit sequence. All additions/multiplications below are modulo 2^64 and right shifts are logical; this mathematical recurrence is the observable contract, not an exposed state layout:

1. Start `s = seed`. For each next_u64, set `s = s + 0x9e3779b97f4a7c15`.
2. Set `z = (s xor (s >> 30)) * 0xbf58476d1ce4e5b9`.
3. Set `z = (z xor (z >> 27)) * 0x94d049bb133111eb`.
4. Return `z xor (z >> 31)`.

| Random operation | Rule |
| :--- | :--- |
| `below(upper = 0)` | Panic without drawing |
| `below(upper > 0)` | Threshold `2^64 mod upper`; draw until value >= threshold; return value mod upper |
| `next_u64` / `below` cost | O(1) / expected constant draws, finite full-cycle bound; no fixed small worst-case draw count |
| Clone Rng | Copy sequence state; isolate future mutation |
| Seeded generator | Reproducible, non-cryptographic |
| `entropy(count)` | Host cryptographic source; unavailable: Err; zero: empty bytes; negative: panic |
| Entropy fallback | No seeded-generator fallback or reproducibility guarantee |

```ril
use ril/random
let mut rng = Random::seeded(0u64)
assert(Random::next_u64(mut rng) == 0xe220a8397b1dcdafu64)
let mut independent = clone(rng)
assert(Random::next_u64(mut rng) == Random::next_u64(mut independent))
```

## Execution Boundaries

```ril
-- Language-owned interfaces, shown here for library discovery:
-- Fiber::yield() -> () @Fiber
-- Div::budget<T>(limit: int, action: fn() -> T) -> T @Div
```

Fiber::yield cooperatively yields without producing a user value.

| Interface | Contract |
| :--- | :--- |
| `Div::budget(limit, action)` | Nonnegative limit; invoke covered computation under a fresh allowance; zero invokes no action |
| Budget coverage | No residual effects/outward capabilities; no foreign calls, I/O, tasks, resource operations, or parallel combinators |
| Exhaustion | Abandon the computation, run required finite cleanup, then request `Div::exhausted()`; resumption is `E0822` |
| Completion | Return the action result; allowance cannot escape with a returned callable |
| Termination | Recovery and cleanup must independently be finite; handling exhaustion alone supplies no proof |

### Structured Concurrency and Panic Containment

```ril
use ril/concurrent::{scope, TaskFault}
fn isolated_value() -> Result<int, TaskFault> @Concurrent {
    scope \mut s -> {
        let task = s.fork(\-> 42)
        task.join()
    }
}
```

#### Normative Rules for Structured Concurrency

```ril
-- ril/concurrent; Scope and Task are scope-owned opaque resources.
pub type Scope
pub type Task<T>
pub fn scope<T>(body: fn(mut Scope) -> Result<T, TaskFault>) -> Result<T, TaskFault> @Concurrent
-- Built-in receiver call contracts, not additional user-defined method syntax:
-- s.fork<T>(action: fn() -> T) -> Task<T> @Concurrent
-- task.join() -> Result<T, TaskFault> @Concurrent
```

| Structured operation | Result |
| :--- | :--- |
| `s.fork(fn() -> T)` | `Task<T>` |
| `task.join()` | `Result<T, TaskFault>` |
| `scope(body)` where body returns `Result<T, TaskFault>` | Same result shape, after children terminate |

All three require `@Concurrent` and forward callback effects. No implicit join, result flattening, or conversion of business errors to panics occurs.
- **Receivers**: `s.fork` borrows its `mut s` receiver. `Task.join` uses result-observation authority, not mutable data access. Ordinary function arguments do not inherit these built-in contracts.
- **Lifetime (`E0606`)**: Children and their Scope/Task handles stay in their owning scope. Handles cannot be cloned, moved to another task, or hidden in escaping aggregates/closures.
- Join a result once. Task control state is external to its stable descriptor; ordinary returned data must satisfy immutable publication. Resources follow explicit transfer contracts.
- **Failure**: Child panic/double fault permanently fails the scope, even after inspection by `join`. Cancel unfinished descendants and active body waits. Any later `fork` cancels the body; returning `Ok` cannot restore success.
- **Cancellation**: Channel and leaf-I/O waits, pending joins, and nested scope waits must wake. Transfer to the scope boundary without resumption; user `with` cannot absorb cancellation.
- A join of the failed task may deliver its fault for inspection, without clearing failure. Other cancelled waits cannot complete successfully.
| Body exit | Before leaving |
| :--- | :--- |
| `Ok` | Wait for all children |
| `Err(TaskFault)`, panic, cancellation, or delimited abort | Cancel children and wait |

Run child cleanups except those abandoned by double fault. A parent panic/abort continues outward after the barrier; this scope does not catch it as a Result.
- **Termination**: The barrier forbids premature exit, not divergence. Preserve the body's and every required child's termination conditions independently of effects. Built-in waits respond to cancellation; divergence outside cancellation points may prevent exit. No finite completion bound is promised. A child's local finite budget may bound eligible child computation, but an enclosing budget cannot contain structured concurrency.
- **Fault Order**: Among actual faults: double fault, then panic, then cancellation. Ties use task creation order, with an explicit body fault first. Cancellation never replaces its cause; different runs may produce different fault sets.
- **Confinement**: Share immutable ordinary data; reject live/mutable data and non-transferable resources (`E0601`). The listed resource exceptions are detached endpoint transfer and the limited immutable Sender clone-source borrow. Child system effects may include Fiber/Concurrent; Div exhaustion and user effects need child-local handlers (`E0615`). Possible divergence is a separate termination condition, not a child effect.
- **Transitive Access (`E0601`)**: Check every possible access through named external state, callees, callbacks, handlers, and cleanup. An immutable callable descriptor does not make its dependencies immutable. Outside live reads and ordinary writes are rejected even when no captured value crosses the boundary. Apply the separately listed resource permissions without extending them to ordinary data.
- **Results (`E0720`)**: `Task<Result<U, E>>` retains inner inspection duties. Normal success must inspect, propagate, or return them; join checks only the outer result. Abnormal unwinding may discard inaccessible/unfinished results, but cannot report success while losing an error.

```ril
-- Module declarations and an invocation fixture inside an owning scope:
type Cell = { mut count: int }
let SNAPSHOT = Cell.{ count: 1 }
let mut global_cell = Cell.{ count: 0 }
fn read_snapshot() -> int &{SNAPSHOT} { SNAPSHOT.count }
fn read_global() -> int &{global_cell} { global_cell.count }
fn write_global() &{mut global_cell} { global_cell.count += 1 }

let task = s.fork(read_snapshot)       -- OK: immutable named dependency
let result = task.join()
match result { Ok(value) -> { assert(value == 1) }, Err(_fault) -> {} }
-- s.fork(read_global)                -- Error [E0601]: outside live state, despite an immutable function value
-- s.fork(write_global)               -- Error [E0601]: outside write
-- s.fork(\-> read_global())          -- Error [E0601]: indirect access has the same origin
let selected = if choose_live { read_global } else { read_snapshot } -- run-time bool input
-- s.fork(selected)                   -- Error [E0601]: one possible dependency is live
```

```ril
pub type PanicInfo = { message: str, index: ?int }
pub type UnwindCause {
    Panicked(PanicInfo),
    EffectAborted,
    Cancelled,
}
pub type DoubleFaultInfo = { primary: UnwindCause, cleanup: PanicInfo }
pub type TaskFault {
    Panicked(PanicInfo),
    Cancelled,
    DoubleFaultFatal(DoubleFaultInfo),
}

fn inspect_business_result() -> Result<Result<int, str>, TaskFault> @Concurrent {
    scope \mut s -> {
        let task = s.fork(\-> {
            let answer: Result<int, str> = Err("domain failure")
            answer
        })
        let business = task.join()?
        Ok(business)                  -- The caller now owns the inner inspection obligation
    }
}
-- scope \mut s -> { s.fork(\-> Err("lost")); Ok() }
-- Error [E0720]: successful scope exit abandons a fallible task result
```


```ril
-- Returning s from a scope, or a closure capturing s, is E0606.
-- Returning a Task<T> handle rather than its joined data is E0606.
-- Capturing a let scoped resource into a returned callback is E0604.
-- Wrapping any such handle in a record does not change these outcomes.
```

### Deterministic Data Parallelism and Divide-and-Conquer Primitives

```ril
-- ril/parallel; requirements below apply to every actual callback.
pub fn map<T, U>(items: []T, transform: fn(T) -> U) -> []U
pub fn map_bounded<T, U>(items: []T, max_concurrency: int, transform: fn(T) -> U) -> []U
pub fn find<T>(items: []T, predicate: fn(T) -> bool) -> ?T
pub fn first<T>(items: []T, predicate: fn(T) -> bool) -> ?T
pub fn any<T>(items: []T, predicate: fn(T) -> bool) -> bool
pub fn fold<T, A>(items: []T, init_acc: fn() -> A,
    fold_local: fn(A, T) -> A, merge_acc: fn(A, A) -> A) -> A
pub fn join<A, B>(left: fn() -> A, right: fn() -> B) -> (A, B)
pub fn join3<A, B, C>(first: fn() -> A, second: fn() -> B, third: fn() -> C) -> (A, B, C)
pub fn for_each<T>(mut items: []T, action: fn(mut T) -> ()) &mut
```

`first` is an alias of predicate-based `find`. Pure collection calls create fresh result storage as appropriate, retain no callbacks, and admit immutable input; `for_each` instead grants the explicitly listed temporary writes. Empty map returns `[]`, empty find/first returns None, empty any returns false, and empty for_each invokes no callback. Work is O(n) invocations plus callbacks, except find/first/any may stop earlier in reference order; join variants have a fixed branch count. Actual scheduling may evaluate additional unobservable speculative branches. No operation provides a wall-clock speedup guarantee.

```ril
use ril/parallel
halt fn square_all(numbers: []f64) -> []f64 {
    numbers |> Parallel::map(\x -> x * x)
}
let first = [10, 20, 30, 40] |> Parallel::find(\x -> x > 25)
assert(first == Some(30))
```

#### The Colorless Parallel Principle and Domain Boundary

Parallel callbacks have no residual effects and must independently be proved finite; empty effect rows alone do not suffice. Unhandled Div exhaustion is an effect violation; unresolved termination is a finite-computation violation (`E0820`). `@Parallel` is invalid (`E0620`). Allow immutable captures and locally handled operations, including a valid finite budget inside an individual callback. Reject outside mutable/live handlers and resource operations; apply each combinator's access contract.

Pure map/find/fold follow their reference evaluation. Disjoint-write join/for_each follow their [completion rule](#declarative-data-parallelism-and-concurrency-bounding); no universal left-fold equivalence applies.

#### Deterministic Reductions and Bit-Exact Floating-Point Trees

`Parallel::fold(items, init_acc, fold_local, merge_acc)` has this reference evaluation:

1. Partition the input by increasing index into consecutive groups of at most 64 elements.
2. For each group in order, call `init_acc()` once and perform `fold_local` from left to right over that group. Finish all groups before starting merges.
3. Merge adjacent group results from left to right at each level. An unpaired final result advances unchanged. Repeat levels until one result remains.
4. Empty input calls `init_acc()` exactly once and returns it. No merge is performed for fewer than two groups.
5. The first fault in this reference order is the visible fault; later reference operations need not be evaluated. A dependent operation is not evaluated after its input failed. A fold-local fault records the source element index; initialization and merge faults use `PanicInfo.index = None`.

This rule applies to non-associative operations as well. Floating-point addition is permitted but is not claimed to be associative or equal to ordinary sequential left folding. Given fixed primitive numeric semantics, the tree and result do not change with scheduling or worker count.

```ril
let total = Parallel::fold(
    [1.0, 2.0, 3.0],
    init_acc: \-> 0.0,
    fold_local: \acc, x -> acc + x,
    merge_acc: \left, right -> left + right,
)
assert(total == 6.0)
```

#### Observational Equivalence and Short-Circuit Determinism

`map` follows element order. `find`, `first`, and `any` stop at the first decisive match or fault in that order. A match suppresses everything to its right; skipped branches may have no outside-observable effects.

#### Canonical Leftmost Panic Precedence Rule

- A pure branch's panic/double fault first becomes a local terminal outcome. Propagate only faults visible in reference evaluation; skipped rightward faults cannot fail the parent.
- Branches own their mutable state and cleanup. Abandoned cleanup must not affect an outside-observable resource (`E0605`).

Wait for all started branches. Propagate the selected panic; a selected double fault fatally fails the owning task or aborts an unsupervised program. Never resume a failed branch or restart abandoned cleanup.

```ril
let found = [0, 1] |> Parallel::find(\x -> {
    if x == 0 { true } else { panic("right branch") }
})
assert(found == Some(0))               -- Even if the right branch ran speculatively
```

The same reference-visibility rule applies if the skipped right branch suffers a double fault in branch-local cleanup. There is no exception that lets speculative fatal outcomes change an otherwise successful leftmost result.

#### Lightweight Divide-and-Conquer (Parallel::join)

`Parallel::join(a, b)` returns `(a(), b())`; `join3` returns three results. Invoke each branch once and wait for all branches.

- Share immutable reads. Temporary parent-data writes require disjoint write/read and write/write regions (`E0619`). Check actual captures; distinct names/indices do not prove separation.
- The parent suspends access to lent regions until completion; other tasks cannot access them. Branch invocation authority is confined and does not create a lasting owner.

#### Declarative Data Parallelism and Concurrency Bounding

- **for_each**: `cells !> Parallel::for_each(\mut cell -> { ... })` explicitly lends each writable element to one invocation. Every element's writable reachable region must be disjoint from every other invocation's reads/writes (`E0619`). Immutable elements or unknown overlapping aliases are rejected; outside mutable captures are rejected (`E0605`).
- **Completion**: join/join3/for_each finish every independent invocation and retain its writes. Then report double fault before panic, breaking ties by branch/index order. There is no rollback or sequential-short-circuit partial-state guarantee.
- **map_bounded**: A positive `max_concurrency` bounds active evaluations without changing pure reference semantics. A non-positive bound panics before any callback invocation.

```ril
type Cell = { mut count: int }
let mut cells = [Cell.{ count: 1 }, Cell.{ count: 2 }]
cells !> Parallel::for_each(\mut cell -> { cell.count *= 2 })
assert(cells[0].count == 2 && cells[1].count == 4)

let original = Cell.{ count: 0 }
let repeated = (original, original)
let mut copy = ^mut clone(repeated)
-- Parallel::join(\-> { copy.0.count += 1 }, \-> { copy.1.count += 1 })
-- Error [E0619]: both branches would write the same copied origin
copy.0.count += 1                     -- Sequential access is valid
```

#### The Absolute Effect-Free Parallel Invariant

Apply effect, access, and termination checks transitively through calls and handlers. Handling Div exhaustion does not by itself prove termination; a valid finite budget certifies only its protected invocation, with finite cleanup and recovery still required. Resource endpoint operations are not pure parallel operations. Only join/for_each grant confined outside write authority; no live aliases escape.

### Structured Concurrency Channels

```ril
use ril/concurrent::{scope, TaskFault}
use ril/concurrent/channel

fn one_message() -> Result<int, TaskFault> @Async {
    scope \mut s -> {
        let (tx, mut rx) = Channel::bounded<int>(1)
        let producer = s.fork(\-> {
            -- Channel::close(tx)     -- Error [E0603]: a child clone-source borrow cannot consume the owner
            let mut local_tx = clone(tx)
            (local_tx !> Channel::send(42))
                ?? \_error -> panic("receiver closed")
            Channel::close(local_tx)
        })
        -- Channel::close(tx)         -- Error [E0603]: producer still holds a clone-source borrow
        let value = (rx !> Channel::recv())
            ?? \_error -> panic("sender closed")
        producer.join()?
        Channel::close(tx)
        Ok(value)
    }
}
```

#### Normative Rules for Structured Channels


The following declarations describe the channel module's contracts (opaque declaration-unit forms):

```ril
-- ril/concurrent/channel
pub type Sender<T>
pub type Receiver<T>
pub type Detached<E>
pub type ChannelError { Closed }
pub fn bounded<T>(capacity: int) -> (Sender<T>, Receiver<T>) @Fiber
pub fn send<T>(mut endpoint: Sender<T>, value: T) -> Result<(), ChannelError> @Fiber &mut
pub fn recv<T>(mut endpoint: Receiver<T>) -> Result<T, ChannelError> @Fiber &mut
pub fn detach<E>(mut endpoint: E) -> Detached<E> @Fiber &mut
pub fn attach<E>(ticket: Detached<E>) -> E @Fiber
pub fn close<E>(endpoint: E) -> () @Fiber
```

In these three generic interface extracts, E is exactly Sender<T> or Receiver<T>; other resource types have no matching contract (`E0908`). Attach returns the transferred writable endpoint authority. Close consumes the named descriptor's existing owner authority, despite its ordinary argument spelling; this is the existing channel-specific contract, not a general consuming parameter mode. Queue bookkeeping is amortized O(1) per message, excluding payload processing and potentially unbounded waits. Detach/attach/close perform finite descriptor transitions, with closure of queued detached payloads proportional to those payloads.

Sender/Receiver/Detached are scope-owned opaque resources. Immutable descriptors may enter `let`; protocol state is external and effect-accessed. These resource contracts do not apply to ordinary data.

| Access or copy | Contract |
| :--- | :--- |
| Send/receive | Writable endpoint, `@Fiber &mut`; one owning task (`E0603`) |
| `clone(Sender<T>)` | `@Fiber`; independent task-local endpoint authority, same channel; no resource-graph isolation guarantee |
| Immutable Sender captured by a child | Clone-source only; no send/close/detach or acquisition of owner authority (`E0603`), even through aggregates/closures |
| Owner close/detach while borrowed | Suspended until every borrowing task's terminal join or the scope's child barrier (`E0603`) |
| Scheduling progress, dropped Task, last textual use | Do not end a clone-source borrow |
| Clone Receiver/Detached; endpoint `clone_immut` | `E0530`, including inside containers |
| Endpoint `derive` | `E0536`, including inside containers |

```ril
-- Within an owning scope; rx has no other usable alias:
let ticket = Channel::detach(mut rx)
-- rx !> Channel::recv()               -- Error [E0603]: authority was transferred
-- clone(ticket)                      -- Error [E0530]: detached authority cannot be duplicated
-- The receiving task can consume ticket once with Channel::attach(ticket).
```

```ril
-- Within one owning scope; resource_rx is an exclusive endpoint and control_tx accepts its Detached descriptor.
let ticket = Channel::detach(mut resource_rx)
let sent = control_tx !> Channel::send(ticket)
match sent { Ok() -> {}, Err(_error) -> {} }
-- Channel::attach(ticket)             -- Error [E0603]: both send outcomes consumed the ticket
```

| Operation (`@Fiber`) | Authority change |
| :--- | :--- |
| `detach(mut endpoint)` | Consume exclusive endpoint; return non-clonable `Detached<Endpoint>` |
| `attach(ticket)` | Consume once; obtain writable endpoint in receiving task |
| Enter `send(ticket)` after argument evaluation | Consume ticket on every outcome; pending send owns it |
| Enqueue / successful receive | Ownership passes to queue / receiver |
| `Err(Closed)` or cancellation before enqueue | Close submitted endpoint once; never restore ticket |
| Receiver close | Close unreceived queued detached endpoints once |

Detach rejects other usable aliases/views/captures and invalidates old paths (`E0603`). Only detached descriptors are transferable resource payloads; `mut`/`^mut` alone never transfer. Transfers and cross-task clones stay within the owning scope's descendants (`E0606`), independently of GC.

Payloads may be scalars, immutable ordinary data (even with field `mut` markers), or one-use detached descriptors. Live data, mutable environments, ordinary write authority, and hidden non-transferable resources are `E0602`.

```ril
-- Within an owning scope; writable rx receives Result<int, str> payloads.
match (rx !> Channel::recv()) {
    Ok(business) -> { let _ = business ?? \_error -> 0 },
    Err(_error) -> {},
}
-- match (rx !> Channel::recv()) { Ok(_) -> {}, Err(_) -> {} }
-- Error [E0720]: only the transport result was inspected
```

| Fallible payload event | Outstanding inspection obligation |
| :--- | :--- |
| Successful send / receive | Passes to queue / received value |
| Send returns `Err(Closed)` | Stays with sender's original value/aliases; no implicit payload return |
| Inspect send/recv's outer Result | Does not inspect a payload Result |
| Normal completion, including another business `Err` | Must preserve or discharge the obligation (`E0720`) |
| Normal receiver close / scope exit | Cannot discard possibly uninspected queued Results (`E0720`) |
| Receive returns `Err(Closed)` | Queue is empty |
| Panic, cancellation, effect abort | Ordinary abnormal-unwinding exemption |

Aliases share one obligation; transmission does not create an independent copy.

| Operation | Result and ordering |
| :--- | :--- |
| `send` | `Result<(), ChannelError>`; closed receiver gives `Err(Closed)` |
| `recv` | `Result<T, ChannelError>`; drain queue, then `Err(Closed)` after all senders close |
| `bounded` | Positive capacity limits queued messages; invalid capacity panics before creation |

Successful sends retain each sender's order; different senders have no global order.

| Closing or cancellation | Rule |
| :--- | :--- |
| `Channel::close` | `@Fiber`; consumes the descriptor's authority and invalidates its aliases |
| Task termination | Close writable local endpoints |
| Scope exit | Close remaining descriptors after the child barrier |
| Automatic close | Structured boundary's `@Fiber` contract; not `on_close` or a separate `let scoped` contract |
| Immutable clone-source Sender | Open until close/scope exit; EOF never depends on GC |
| Cancel blocked send/recv | Non-resumable scope exit; no fabricated message/error. Producer failure wakes a body blocked on recv |

## Testing

```ril
-- ril/test
pub fn assert_eq<T>(actual: T, expected: T, message: str = "values differ")
pub fn assert_ne<T>(actual: T, unexpected: T, message: str = "values are equal")
pub fn assert_some<T>(value: Option<T>, message: str = "expected Some") -> T
pub fn assert_ok<T, E>(value: Result<T, E>, message: str = "expected Ok") -> T
```

Equality helpers use the language's structural equality and preserve its unsupported-type diagnostics; they have no residual effect. Assert_some/assert_ok inspect the outer tag and return its payload, or panic with message. They do not deep-inspect nested Results. Comparisons are finite under the language's equality contract; tag assertions are O(1). These functions do not catch panics synchronously. Only the structured task boundary below contains a child panic as a value.

### Test Conventions and Execution Protocol

Test entry points are ordinary public functions conforming to the naming prefix `test_*` and returning either `()` or `Result<(), E>`. Test functions evaluate within isolated activation frames and enforce domain invariants via standard assertions:

- **Pure & Direct Tests**: Functions returning `()` verify invariants using deterministic runtime panics on breach (`assert`).
- **Fallible Tests**: Functions returning `Result<(), E>` enable cascading error propagation via postfix `?`. Returning `Err(e)` indicates test assertion failure.
- **Hermetic Scoped Mocking**: Environmental algebraic effects are mocked within standard lexical blocks `{ with HandlerSpec; logic }`. The handler is automatically popped upon exiting the block. Missing handlers are rejected statically; a mock handler may explicitly panic on an unexpected but handled request.
- **Panic Isolation Assertion**: Asserting that defective operations trigger deterministic runtime panics is evaluated across structured concurrency task boundaries (`s.fork` inside `scope`), capturing faults into `TaskFault::Panicked` without violating synchronous frame panic isolation.
- **Resource Lifecycle**: Ephemeral and in-memory test resources use `let scoped` bindings, guaranteeing strict LIFO destruction. Effectful I/O transactions utilize higher-order wrapper functions.

```ril
use ril/array::{push}
use ril/num

-- Direct unit test returning ():
pub fn test_array_push() -> () {
    let mut items = [1, 2]
    items !> push(3)
    assert(len(items) == 3, "expected 3 items")
}

-- Fallible unit test with '?' error cascade:
pub fn test_parse_pipeline() -> Result<(), Num::NumError> {
    let raw = "100"
    let parsed = Num::parse_int(raw)?
    assert(parsed == 100, "expected parsed integer 100")
    Ok()
}

-- Hermetic sandbox mock testing via scoped handler block:
eff Database {
    query(sql: str) -> Result<str, str>,
}

pub fn test_user_query() -> Result<(), str> {
    let outcome = {
        with Database::query(sql) -> {
            if sql == "SELECT user FROM users WHERE id = 1" {
                resume Ok("Alice")
            } else {
                -- Hermetic Sandbox: unexpected calls trigger deterministic defect panic
                panic("Unexpected mock query: {sql}")
            }
        }

        let user = Database::query("SELECT user FROM users WHERE id = 1")?
        assert(user == "Alice", "user mismatch")
        Ok()
    }
    outcome
}

-- Scoped resource cleanup following strict LIFO order:
type Resource = { mut name: str, mut on_close: fn() -> () }
pub fn test_scoped_cleanup() -> Result<(), str> {
    let mut trace: []str = []
    {
        let scoped mut res = Resource.{
            name: "test_db",
            on_close: \-> trace !> push("db_closed"),
        }
        trace !> push("test_executed")
    }
    assert(trace == ["test_executed", "db_closed"], "cleanup must follow LIFO order")
    Ok()
}

-- Defect panic assertion via structured concurrency boundary:
use ril/concurrent::{scope, TaskFault}

pub fn test_out_of_bounds_defect() -> Result<(), str> @Concurrent {
    let outcome = scope(\mut s -> {
        s.fork(\-> {
            let arr = [1, 2]
            let _ = arr[5]             -- Triggers defect panic: index out of bounds
        })
        Ok()
    })

    match outcome {
        Err(TaskFault::Panicked(info)) -> {
            let _ = info              -- Payload text is explanatory, not a conformance assertion
            Ok()
        },
        _ -> panic("expected operation to panic, but completed normally"),
    }
}
```

## Static Availability

```ril
use ril/clock
meta let COUNT = len("é🙂")
meta let WORDS = String::split("a,b", ",")
meta let SIZES = Array::map(WORDS, \word -> len(word))
meta let _ = assert(COUNT == 2 && SIZES == [1, 1])
-- meta let NOW = Clock::now()          -- Error [E0810]: run-time-only call
```

The table lists every dual-phase library operation in this version. An unlisted pure function remains run-time-only.

| Entry | Static availability |
| :--- | :--- |
| `len`, `assert` | Both phases; failed static assertion is E0830 |
| Array `first`, `get`, `contains`, `reverse`, `concat`, `map`, `filter`, `fold`, `find`, `any`, `all`, `for_each` | Both phases with immutable symbolic data and statically admissible callbacks |
| Map `get`, `contains`, `keys`, `values`, `entries`, `from` | Both phases with immutable symbolic data |
| Every String function listed in this document | Both phases with immutable symbolic data |
| `Array::Elem`, `Map::Key`, `Map::Value`, `Set::Elem` | Type functions only, under ordinary type-function invocation rules |
| Other library callables, including mutation families and newly added pure modules | Run-time only unless individually specified otherwise in a future version |

The ordinary constructor/type uses of Option, Result, Immut, and nominal types retain the language's phase rules; they are not new function exceptions. Static callbacks cannot invoke arbitrary run-time functions, capture live storage, or install run-time handlers. Static evaluation has its own budget and E0811, independent of Div. Static and run-time instances of a dual-phase function have the same data/order behavior on the same admissible inputs.

## Local Tooling Composition

This complete program uses only the public library surface. Its three arguments are a UTF-8 source path, binary output path, and an explicit executable path. It records Unicode scalar positions and byte offsets, stores a frequency index, serializes and checks fixed-width data, writes it, and passes the output path as one child argument. These are ordinary data-processing operations; no compiler-specific structures or execution machinery are prescribed.

```ril
use ril/env
use ril/os
use ril/path
use ril/file
use ril/io
use ril/num
use ril/bytes
use ril/encoding/binary
use ril/process

type Position = { scalar: u32, scalar_index: int, byte_offset: int }

pub fn main() -> Result<(), str> @Fiber {
    let args = Env::args()
    if len(args) != 3 { return Err("expected source, output, and executable paths") }
    let source_path = Path::from_native(args[0])
    let output_path = Path::from_native(args[1])
    let program_path = Path::from_native(args[2])
    let text = Results::map_err(File::read_text(source_path), Io::error_text)?

    let mut positions: []Position = []
    let mut counts: [u32: int] = [:]
    var scalar_index = 0
    var byte_index = 0
    for String::scalars(text) as scalar {
        positions !> Array::push(Position.{
            scalar: scalar, scalar_index: scalar_index, byte_offset: byte_index,
        })
        let previous = Map::get(counts, scalar) ?? 0
        counts !> Map::set(scalar, previous + 1)
        scalar_index += 1
        byte_index += if scalar <= 0x7Fu32 { 1 }
            else if scalar <= 0x7FFu32 { 2 }
            else if scalar <= 0xFFFFu32 { 3 }
            else { 4 }
    }
    assert(byte_index == String::byte_len(text))

    let mut binary: []u8 = []
    binary !> Binary::write_bytes(b"RILP")
    let count = Results::map_err(Num::convert<int, u64>(len(positions)), \_error -> "too many positions")?
    binary !> Binary::write_u64(count, Binary::ByteOrder::Little)
    for positions as position {
        binary !> Binary::write_u32(position.scalar, Binary::ByteOrder::Little)
        let offset = Results::map_err(Num::convert<int, u64>(position.byte_offset), \_error -> "offset overflow")?
        binary !> Binary::write_u64(offset, Binary::ByteOrder::Little)
    }
    let data = Bytes::from_array(binary)
    Results::map_err(File::write_bytes(output_path, data), Io::error_text)?
    let reread = Results::map_err(File::read_bytes(output_path), Io::error_text)?
    assert(reread == data)
    let mut cursor = Binary::cursor(reread)
    assert(Binary::read_bytes(mut cursor, 4) is Ok(b"RILP"))
    let decoded_count = Results::map_err(Binary::read_u64(mut cursor, Binary::ByteOrder::Little), \_error -> "invalid count")?
    assert(decoded_count == count)
    for positions as position {
        let decoded_scalar = Results::map_err(Binary::read_u32(mut cursor, Binary::ByteOrder::Little), \_error -> "invalid scalar")?
        let decoded_offset = Results::map_err(Binary::read_u64(mut cursor, Binary::ByteOrder::Little), \_error -> "invalid offset")?
        let expected_offset = Results::map_err(Num::convert<int, u64>(position.byte_offset), \_error -> "offset overflow")?
        assert(decoded_scalar == position.scalar && decoded_offset == expected_offset)
    }
    assert(Binary::remaining(cursor) == 0)

    let command = Process::command(program_path, [Path::native(output_path)])
    let output = Results::map_err(Process::run(command), \_error -> "child operation failed")?
    if !Process::success(output.status) { return Err("child exited unsuccessfully") }
    println("{len(positions)} scalars, {len(counts)} distinct values")
    Ok()
}
```

For source `Aé🙂A`, positions are `(U+0041,0,0)`, `(U+00E9,1,1)`, `(U+1F642,2,3)`, `(U+0041,3,7)`; the final byte length is 8 and counts are 2, 1, 1 in first-insertion order. Empty source produces the header with count zero. Invalid UTF-8 fails before writing output; a write failure prevents child invocation. A child nonzero exit produces the final Err branch. Output replacement and earlier writes are not rolled back after a later failure.

## Conformance Cases

Each row is a required behavioral fixture in addition to the code examples. Environmental fixtures supply controlled files, streams, child programs, or native platform values; message wording and wall-clock timing are not asserted.

| Area | Required cases |
| :--- | :--- |
| Prelude | Explicit import/re-export preserves declaration identity; local shadowing follows lexical scope; File/Clock/Test require imports |
| Containers | Empty pop/find/fold; last duplicate map value at first position; remove/reinsert appends; Set algebra order; live references gain no writer |
| Callbacks | Empty input invokes none; short circuit stops; mutable environment needs explicit mut; panic retains earlier outside writes |
| Ordering | Stable equal keys; first duplicate search index; absent-key insertion position; NaN and signed-zero total order |
| Iteration | Done is sticky in Cursor; take zero never pulls; filter can require multiple pulls; no escaped resume; nested Result cannot be discarded |
| Text | Empty separator/pattern; supplementary scalars; combining sequences remain unnormalized; byte position inside multibyte scalar is None; CRLF/final LF behavior |
| Encoding | Malformed UTF-8 and surrogate values; exact failure offsets; binary endianness; truncated/overflow/redundant ULEB128 leaves cursor unchanged; SHA-256 known vector |
| Numbers | Every integer min/max and first out-of-range value; invalid radix; float negative zero/NaN/infinity; parse/format round trips |
| I/O | Last bytes plus EOF; zero request; short reads; partial write plus error without duplicate prefix; buffered retry retains suffix; cancellation does not report success |
| Files | Missing/denied file, exclusive creation collision, invalid UTF-8, seek failure, explicit close error, release after panic, sorted directory entries, no recursive deletion |
| Paths/environment | Non-Unicode native names round-trip; NUL rejected only at OS boundary; drive-relative/rooted/UNC/verbatim paths; symlink-sensitive lexical normalization; absent versus empty env |
| Processes | Empty/space/quote arguments; launch failure versus exit 7; independent captured streams; capture limit; explicit env/cwd; cancellation and owner cleanup |
| Time/random | Timestamp normalization and overflow; negative sleep; monotonic domain mismatch; deterministic seeded vector; entropy failure |
| Execution | Existing task barrier/fault precedence, endpoint transfers, Result payload obligations, fixed parallel fold tree, skipped rightward faults |
| Static use | Listed pure combinators valid with symbolic inputs; new run-time-only functions remain E0810; static assertion E0830 and budget E0811 |
