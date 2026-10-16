# Complete stream receiver schemas

`Io::read_all` and `Io::write_all` retain the receiver's complete declared
`SourceTypeWitness` when checking `ReadOps<R>` or `WriteOps<W>`. Fixed dimensions,
nested and empty arrays, callable modes, and readonly wrappers are preserved.
An erased semantic type is a fallback only when no array, callable, open row,
applied type, projection, or unresolved identity can be lost. Missing complete
evidence remains NotImplemented.

Type identity and actual storage are independent. Before probing the supplied
callback or summarizing repeated calls, the existing storage checker verifies
the actual receiver against that declaration. Successful checks retain fixed
scratch cardinality through the existing summary. Physical fixed backing never
turns a declared dynamic view into a fixed type. The same array checker now
visits `Immut<T>` transparently, including through Option and Result; wrappers
change authority without erasing the independent cardinality obligation.

Known zero-argument native type names use the existing exact builtin type table.
This permits complete schemas containing `File::Handle` without treating the
resource as freely copyable. Unknown names and builtin type arguments do not
gain identity evidence. The independent SourceTypeWitness validator uses the
same recognition rule and rejects mutated consistent-key forged names.

Callback invocation still uses the actual receiver graph, parameter modes,
temporary borrow, capability bounds, repeated-call stability, resource rules,
and Result duties. An ambient state read does not satisfy the stream callback's
`&mut` bound. Readonly paths remain readonly; a fixed scratch array cannot be
resized by the callback or after the helper.

Compiler `io_fixed_receivers` covers nine groups. CLI `io_fixed_receivers`
executes seven fixtures: the original fixed receiver and dynamic control,
nested/empty arrays, a writer including empty data, a dynamic view over fixed
backing, a readonly ambient alias, and a scoped File resource. Evidence and
original before/after JSON live under `target/implementation-gap-audit/`.
All nine Source/Core groups and seven native fixtures passed on Windows and
Linux, together with the adjacent fixed-array and buffered-origin regressions.

Normal completion of both all-stream helpers guarantees at least one callback,
including validation of an empty `write_all` input. Their Result-family finish
therefore retains actual first-entry inspections of pre-existing producers.
It preserves neither callback return flags nor abnormal flags as a waiver of
caller debt. New callback producers still require per-iteration inspection and
escape checks. Other repeated callbacks and loops retain their zero-entry
possibility.

The byte-preserved `io_callback_result_inspection.ril` and the empty-writer
counterpart previously produced false E0720 diagnostics; before JSON and the
compiler hash are saved under `target/implementation-gap-audit/`. Three compiler
groups now pass on both platforms, including zero-entry, unreachable inspection,
and uninspected-clone counterexamples. Both legal programs also executed as
native programs on both platforms. The latest component gates are
`target/io-guaranteed-native-windows-v3.log` and
`target/static-bound-and-channel-io-native-linux-v1.log`; each actually builds
and executes both legal programs. The earlier Windows integration evidence in
`target/io-guaranteed-and-record-native-windows-v2.log` is retained separately.
