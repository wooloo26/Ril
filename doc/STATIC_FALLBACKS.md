# Static fallback evidence

Optional fallback evaluates its left expression once. A Some path returns the
existing payload; a None path evaluates the fallback expression. The universal
Result-flow checker splits an unknown optional using its immutable presence
identity, preserving repeated observations and aliases. Presence alone never
inspects a nested Result. Returning a payload retains its original producer;
only the reached fallback can create another producer.

Typing uses the Optional payload as the receiving context. Complete dimensions
and callable source interfaces remain necessary. Fresh arrays may receive a
declared fixed shape; existing dynamic arrays cannot acquire one from their
backing element count. The evaluator copies the selected immutable handle and
uses complete source schemas for a reached fallback. These operations do not
grant capability authority or use actual Some inputs to prove a universal body.

Fallback control boundaries are checked from bounded owned AST traversal.
Return and propagation cannot escape the fallback; last/next cannot target a
loop outside it. Nested callables and loops keep their own boundaries. Invalid
transfers report E0710, unsupported operand families E0714, and a raw-value
Result fallback E0711. A Result error-consuming handler still needs its separate
complete proof and remains explicitly NotImplemented.

The v5 component tests exposed an incorrect acceptance of a direct outer return
inside a static fallback. Its exact source, frozen test executable hash and
actual passing output are retained under
`target/static-coalescing-outward-return-before*`. This is an implementation
defect, not a SPEC contradiction. The regression now requires E0710, including
dead branches, outer-loop transfers and propagation. Local callable returns
and local loops have separate source/AST controls.

Both v7 integration logs pass the 441 compiler library tests (one explicit
ignore), all seven static template/fallback groups, and the uninspected-Result
negative group. They still fail an unrelated alias-wrapper regression and an
incorrect test entry missing its global state annotation, so neither log is a
successful combined gate. The entry annotation was corrected without changing
compiler rules; both groups in `static_optional_fallback` then pass against the
same frozen compiler libraries in
`target/static-optional-fallback-source-windows-v8.log` and
`target/static-optional-fallback-source-linux-v8.log`.

The v9 combined gate then passes 590 Rust tests on each host, with one explicit
ignore. The old alias wrapper is restored without changing its fixture or
dropping the actual callable's labels/defaults. The Optional Result fallback
program executes successfully on Windows and Linux, including its original
producer and reached fallback values, in
`target/scoped-write-template-native-windows-v9-static-optional-fallback.log`
and `target/scoped-write-template-native-linux-v9-static_optional_fallback.log`.
All ten native test executables succeed on both hosts; their 36 distinct
positive sources and 38 entry executions retain unchanged compiler/runtime/test
hashes. This is component evidence, not full SPEC/STD conformance.
