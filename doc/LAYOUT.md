# Internal value and storage layout

`ril-ir::layout` defines layout version 1 for the abstract `pointer32` and
`pointer64` targets. Both declared x86-64 native targets use the `pointer64`
value layout. Sizes and offsets use checked target arithmetic; the host's
pointer size and Rust structure layout do not determine them.

These are compiler implementation contracts. They provide no source-level
field offsets, packed layout, or foreign exchange ABI. The checker must reject
static-only materialization before selecting a runtime representation.
`byte_size` will query a checked type's value representation, not the storage
reachable through its handles. The current driver does not yet implement
that query or runtime execution.

## Value representations

Here `P` is the selected target's pointer width in bytes.

| Representation | Size | Alignment | Managed references |
| --- | --- | --- | --- |
| Unit / never | 0 | 1 | None |
| Boolean | 1 | 1 | None |
| Fixed integer | Declared width / 8 | Size | None |
| f32 / f64 | 4 / 8 | Size | None |
| bigint, str, bytes | P | P | Offset 0 |
| Shared-object root | P | P | Offset 0 |
| Callable | 2P | P | Environment at offset P |
| Integer range | Two endpoints and one inclusive byte, padded to endpoint alignment | Endpoint alignment | Endpoint references for bigint ranges |

`i64` and `u64` retain eight-byte size and alignment on both abstract targets.
Zero size for `never` supplies no inhabitant and permits no normal value
construction. Nominal and ordinary opaque wrappers keep their checked
representation; wrapping does not add an object root. Nonempty products,
collections, and sum instances use managed shared-object handles.

Immutable bigint, string, and byte backing objects are traced even though the
Ril values have copy-by-value semantics and no shared-object identity. Copying
their handles cannot create write or observation authority. A callable's code
pointer is not a GC reference; its nullable environment pointer is.

## Fixed object storage

An object starts with a descriptor pointer and one flags word, each of size P.
The descriptor and flags are not managed references. Descriptor ownership
must outlive all objects using it. The heap registry owns allocation records;
no linked-list pointer is implicit in this header.

Each payload field starts at its value alignment. Final padding makes the
allocation size a multiple of its maximum alignment, including the header.
Field and trace offsets are relative to the object handle and include the
header. The layout builder preserves the supplied logical field order; the
checker and lowering determine that order without changing source evaluation
order.

Trace offsets identify strong managed-pointer slots, including those inside
value representations such as callables and bigint ranges. A collector skips
null slots. Tracing a pointer uses the target object's descriptor. Descriptors
do not expose Ril type tokens or runtime reflection.

## Repeated buffers

A buffer adds an eight-byte `i64` count after the common header and aligns its
element storage to the element representation. Its stride includes all value
padding. A repeated trace description records the element layout and count;
it does not allocate one descriptor entry per element. Leaf and zero-sized
buffers therefore have an empty trace iterator even at large logical extents.

Counts must fit nonnegative `i64`. All size multiplication, alignment, and
prefix addition are checked. An allocation must also fit the selected target
address space: at most `u32::MAX` bytes for `pointer32` and `i64::MAX` for the
64-bit layouts. These representational limits do not promise that an
allocation can be physically satisfied.

Layout overflow, an excessive extent, and an excessive target allocation are
distinct failures. Consumers must preserve that distinction when reporting a
build failure or an execution allocation fault. Source-level collection
extent rules still apply independently.

## Floating values

`ril-ir::float` uses private canonical bit representations for f32 and f64.
Every input and arithmetic result normalizes NaNs to the positive quiet-NaN
patterns in SPEC. Arithmetic rounds at each operation; no fused operation is
implicit. Subnormals and signed zero remain represented.

The value types deliberately do not implement Rust equality. IEEE comparison
is explicit: signed zeros compare equal and NaNs compare unequal/unordered.
Static argument identity instead uses `FloatKey`, retaining width and zero
sign while normalizing NaNs. Binary decoding and explicit narrowing pass
through the same canonicalization. Conversion eligibility remains a checker
and primitive-contract obligation.

Safe division and remainder reject either zero sign with `None`; otherwise
they preserve the IEEE result, including canonical NaN. Ordinary division
and remainder retain IEEE behavior without an integer-style zero panic.
