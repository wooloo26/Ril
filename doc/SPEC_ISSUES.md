# Specification issues requiring later resolution

Record a contradiction here only when two normative requirements cannot both be
satisfied. Include exact SPEC/STD sections, a minimal example, observed conflict,
the conservative temporary behavior, and the later decision needed. Do not
silently change the specification or treat an implementation gap as a conflict.

No confirmed contradiction has been recorded yet.

## Clarification: runtime references to meta constants

SPEC's **Compile-Time Computation** permits a `meta let` result to be used as an
immutable runtime constant. **External State Tracking** separately requires a
named source group when accessing module-level or captured bindings. The former
does not explicitly exempt meta constants from the latter, so these requirements
can currently be satisfied together:

```ril
meta let ANSWER = 42
fn answer() -> int &{ANSWER} { ANSWER }
```

The implementation retains the named-source requirement for a runtime reference
to `ANSWER`; it does not silently erase capability obligations through static
evaluation. A later specification decision may explicitly exempt such references.
This is a clarification request, not a confirmed contradiction.

## Clarification: immutable Parallel inputs in ordinary parameter types

STD **Deterministic Data Parallelism and Divide-and-Conquer Primitives** requires
immutable input for pure collection operations, and SPEC's identically named
section rejects outside live dependencies. The STD example immediately below
the signatures instead accepts an ordinary read parameter:

```ril
halt fn square_all(numbers: []f64) -> []f64 {
    numbers |> Parallel::map(\x -> x * x)
}
```

An ordinary read-only array parameter can denote a live view whose caller still
owns a writer; read permission alone does not establish deep immutability. The
current checker therefore requires an immutable witness at this boundary, such
as `numbers: Immut<[]f64>` or `clone_immut(numbers)`, and rejects an arbitrary live
read parameter with E0605. It never turns a read-only view into an immutable
graph. A later clarification should state whether this example needs an
`Immut` parameter, or whether `halt` explicitly entails a new immutable-input
contract enforced at every call. This is a clarification request, not a confirmed
contradiction.

## Clarification: generic buffered readers and stream-position operations

STD **Buffered Streams** says unread data or a deferred error reserves the
reader's stream position, and direct stream reads or switching reader/operation
panic before another read. `ReadOps<R>` accepts an ordinary user callable over
an arbitrary mutable `R`; the language does not declare a separate stream-position
field or a read-operation role for every other callable over that same `R`.

For example, after `read_buffered(mut buffer, mut reader, .{ read: read1 }, 1)`,
`read2(mut reader, 1)` may consume the same memory-reader cursor, or may only
observe unrelated data. A matching argument/result signature alone cannot
distinguish these behaviors. The implementation tracks the selected callable and
actual delegated file-read endpoints; a different custom implementation never
selected as `ReadOps` is an outstanding coverage gap, not a proven-safe bypass.
An eventual contract should define how such a callable denotes the same stream
position, without forbidding all pure observations of the receiver.

`File::seek` also changes a stream position, but the buffered table explicitly
names direct reads and switching reader/operation. Clarify whether a seek during
unread buffering must panic, or how it affects the pending buffer. Neither issue
has been used to silently change the specification. These are clarification
requests, not confirmed contradictory normative requirements.
