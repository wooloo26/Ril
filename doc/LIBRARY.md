# Compiler library contracts

The canonical declarations live under `crates/ril-compiler/library`. The
compiler inventory in `src/library.rs` binds their declaration identities to
native primitives or source bodies and records static, runtime, or dual-phase
admission. A user function with the same spelling receives its ordinary call
family. A source-bodied operation executes its Ril body in either admitted
phase, preserving source call, loop, callback, and fault order.

These contracts cover the collection modules currently present. Remaining
resource, task, parallel, and environment contracts must be added before the
release library can pass its checking and execution gates. The frontend checks
the declarations and their identities; it does not yet prove their contracts
or execute them.

## Shared collection rules

Array and map schemas retain their declared modes. Storage operations select
concrete reception from the checked destination schema. An existing instance
keeps that schema across replacement. `via` does not grant source authority.
New and retained inputs require the construction, origin, sharing, lifetime,
and exclusivity proofs in [SPEC](SPEC.md#homogeneous-storage-authority).

Map keys and set elements receive deeply immutable ordinary data and obey the
[structural key rules](SPEC.md#relational-and-equality-operators). Traversal
uses first-insertion order. Replacing a map entry or reinserting a set member
preserves its position. Removing and subsequently reinserting a member puts
it at the end. Array traversal uses increasing index order.

All construction and growth obey the `i64` collection extent limit. Invalid
bounds, negative lengths, and extent overflow panic before structural change.
Resource and scoped authority do not gain copying, transfer, or cleanup rights
from a collection operation.

## Array

`Array` is ambient and explicitly importable from `ril/array`. Its operations
are dual-phase; static invocations must use static data and callbacks. Its
`Elem` type function returns the element data type, or `never` for a non-array.

| Operation | Implementation | Behavior |
| --- | --- | --- |
| `push` | Native primitive | Append one received element; mutate the container and record any conditional retained-source obligation |
| `insert` | Native primitive | Insert before an index in `0..=len`; shift subsequent elements while preserving their identities and modes |
| `pop` | Native primitive | Remove the last element; return `None` when empty. Successful payload authority follows the concrete schema and verified detach or retained-source proof |
| `truncate` | Native primitive | Keep the first `min(length, len)` elements; a negative length panics |
| `first` | Ril body | Safe lookup of index zero; preserve the returned element's possible origins and bounded access |
| `contains` | Ril body | Test equality in increasing index order; stop on the first equal element |
| `map` | Ril body | Invoke the callback once per visited element and append its ordinary result to a new array |
| `filter` | Ril body | Invoke the predicate once per visited element; append those for which it returns true to a new array |
| `fold` | Ril body | Start with `initial`, then replace the accumulator with each callback result in source order |
| `reverse` | Ril body | Allocate a new array with the ordinary elements in reverse order |

`map`, `filter`, and `fold` accept a `via` callback handle with an open latent
contract. Each invocation requires the actual handle authority and forwards
its effects and state obligations. A mutable environment still needs an
explicit caller marker; static callbacks cannot capture live runtime data.
Normal callback results undergo the declared ordinary reception. The source
bodies determine callback order and stop immediately on an abnormal exit.

Push, insert, pop, and truncate require structural-mutation authority. Active
iteration and observation restrictions remain applicable. In particular,
reading an element through `first` grants no detach proof, whereas a successful
exclusive `pop` can carry one only after the storage handoff checks.

The native storage operations are finite on eligible ordinary-data graphs.
Within `Div`, they add no repeated work hidden behind an uncharged infinite
primitive. Source algorithm entries, iteration tests, and callbacks retain
their specified charges. Finiteness and coverage of callbacks are checked
separately; dual-phase admission alone proves neither.

## Map

`Map` is ambient and explicitly importable from `ril/map`. Its operations are
dual-phase Ril bodies. `Key` and `Value` extract the corresponding data types,
or produce `never` for a non-map.

| Operation | Behavior |
| --- | --- |
| `get` | Safe lookup yielding `None` for an absent key; preserve the selected value's modes and origins |
| `set` | Insert or replace via ordinary bracket assignment under the existing value schema |
| `keys` | Allocate a new array of immutable keys in first-insertion order |
| `values` | Allocate a new array in first-insertion order, preserving the visited values' bounded modes and possible origins |

The `values` result has independent array storage. Its root freshness does not
establish isolation from mutable or observed contained objects. Observing a
live map does not freeze it or supply write authority to the result.

## Set

The prelude's source-defined `Set<T>` is an opaque ordinary-data type. The
`ril/set` import and the ambient `Set` namespace refer to that same declaration.
Its map representation is private to its exact defining scope. The native
operations implement the checked set contract without exposing that
representation. `Elem` extracts its type argument or returns `never`.

All set operations are dual-phase. Element eligibility follows the map-key
rules, including structural equality and supported cyclic ordinary-data keys.

| Operation | Implementation | Behavior |
| --- | --- | --- |
| `empty` | Native primitive | Allocate an empty set |
| `insert` | Native primitive | Insert an absent member at the end; return whether insertion occurred |
| `contains` | Native primitive | Return whether an equal member is present |
| `remove` | Native primitive | Remove an equal member if present; return whether removal occurred |
| `to_array` | Native primitive | Allocate an ordinary array of members in first-insertion order |
| `from` | Ril body | Create an empty set and insert array elements in order; keep the first occurrence of each member |

Mutation requires temporary writable access and contributes `&mut`; read
operations admit ordinary immutable reception or explicit observation.
These finite ordinary-data primitives remain subject to the same `Div`,
extent, phase, and structural-mutation rules as other collections.
