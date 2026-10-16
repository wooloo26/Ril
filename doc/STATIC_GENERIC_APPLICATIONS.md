# Static generic applications

Static generic calls now use production type-selection and receiving paths,
rather than a blanket rejection of constrained meta definitions. Ordinary
typing, universal Result flow, evaluated invocation, and receiving interfaces
remain separate checks.

The current component checkpoint is v30 on Windows MSVC x86_64 and Linux GNU
x86_64: each host passes 679 Rust tests across 25 compiler library/Source
targets, with one explicit pre-existing ignore. Fresh native execution passes
17 executables, 22 Rust tests, 49 distinct positive sources and 53 entry jobs
per host. The compiler's all-target Clippy gate also passes with `-D warnings`.
These scoped results include safety regressions that expect NI; they do not
claim all language cases or the whole workspace are implemented.

## Lexical identities and applications

`typing::bounds::BoundEnvironment` keeps genuine type binders as
`StaticBinderId { declaration, index, sort }` and bound rows as
`StaticRowId { declaration, ordinal }`. A visible name can be shadowed without
changing the identity of an already typed value. Implicit residual rows never
invent a position in the declaration's generic parameter list.
The private sort distinguishes `Type` from scalar `ConstInt`. Existing Type
keys keep their prior encoding; const IDs use a separate namespace. Shared
effect/type argument keys have not gained symbolic const extents.

`Typer::check_function_application` consumes the actual application plan,
ordinary types, optional complete source witnesses, explicit arguments, captured
and caller scopes, and a real `u64` activation identity. One transactional row
solver handles every bound in the call. Its flexible residuals are fresh for
that activation; caller tails stay rigid. A closed residual can select a closed
type witness. An open residual remains an open row equation and provides no
absence, freshness, resource, Result, or permission proof.

`named_application_scope_at` prepares source-written argument contexts using a
caller-supplied activation identity. The static Result engine supplies its real
owner identity. The ordinary Typer wrapper allocates an identity from its shared
analysis sequence. Neither uses a span or an array's allocation counter.
Its `ExpectedResult` parameter transports the ordinary hint and optional full
source context as distinct fields, without changing selection priority.

## Complete type evidence

`selected_types` and `selected_rows` retain immutable
`Arc<SourceTypeWitness>` values only for complete closed selections.
`type_arguments` can instead retain an independently registered caller generic.
`row_arguments` retains the solved row, including a rigid open tail.

`complete_source_syntax` substitutes already selected complete syntax and runs
the pure alias normalizer. It does not evaluate a type function or inspect the
evaluator's final argument values to prove a template. Unknown syntax returns no
closed witness. The application checks complete root schemas as well as inferred
child types: a dynamic array that currently has two elements does not satisfy a
declared `[2]T` input. Callable modes and qualifications cannot disappear in an
erased ordinary type.

Fresh array constructors can receive a written fixed construction context.
The declared length is checked against their actual cardinality before that
schema is installed. Existing handles do not take this path. Closed witnesses,
ordinary type copies, and selected-row copies have separate finite admission;
implementation exhaustion is NI, never successful verification.

Local schema bindings explicitly retain `None` tombstones. An unknown local
that shadows a global cannot recover the global's complete array or callable
schema merely because their ordinary types look alike.

The current construction batch also supplies known record-bound field types to
fresh constructors. A required `i8` field selects a fresh numeric literal as
`i8`; required slot declarations are installed on the newly allocated shell.
Stored numbers and existing records keep their prior selections and slot modes.
Spread children keep their identities, and explicit fields override spreads
regardless of written order. This operation supplies no child write authority.
The construction source tests pass on `pointer32` and `pointer64`, and their
accepted program lowers to Core. Four source negatives reject a stored readonly
slot, a stored default-`int` number, a spread default-`int` member, and an `i8`
literal overflow with the actual mismatch/range diagnostics. Both Windows and
Linux native execution pass the fixture's direct, spread, explicit-override,
and block constructor checks.

The Windows integration gate in
`target/optional-and-bound-integration-windows-v4.log` completed with 414 library
tests passing and one pre-existing ignored test; its source gates passed too.
That library gate includes all 21 focused type-application tests. The independent
fresh construction executable results are in
`target/static-bound-construction-native-linux-v2.log` and
`target/optional-fresh-native-windows-v4.log`. Both source groups also pass in
`target/optional-and-bound-integration-linux-v4.log`. These are scoped integration
results, not a claim that the remaining generic sorts or the full language
corpus are complete.

## Callable interfaces

Canonical callable type identity is separate from labels and default arguments.
Two functions with the same parameter/result types can still have different
call interfaces. A genuine `T` receiving position preserves the actual
interface; a source-written `fn(...)` position supplies its declared view and
erases declaration defaults.

`generic_receiving::for_types` produces a pure receiving mask by expanding
aliases with temporary opaque markers for registered generic positions. The
markers are private receiving metadata, not closed witnesses or permission
facts. `transparent` and `child` preserve these positions through `Immut`
wrappers. Unproved alias expansion remains NI.

Prepared named calls retain both raw and resolved signatures. Resolved syntax
checks shape and numeric contexts; raw syntax determines which receiving
positions are generic. Parameter and return receiving do not reevaluate a
computed type solely to recover that distinction.

For callable-containing returns, the Typer derives a type-level interface
summary using the actual argument interfaces. This does not execute the body
and does not replace its universal type or Result proof. Recursive interface
dependencies without a solved fixed point remain NI. The evaluated path keeps
the actual callable targets and uses the same receiving mask.

Focused tests exercise direct and alias-wrapped `first(left = 1)` /
`second(right = 2)` inputs, preserving the returned second function's `right`
label and default. Separate negatives ensure an explicit `fn(renamed: int)`
view still rejects `right` and omitted arguments.

## Type arguments selected by bounded members

A selected argument to `T: { item: U, ..R }` supplies the complete schema of
`item` as a constraint on `U`. The pure application follows existing structural
inference through arrays, tuples, options, records, and Result types. It repeats
member selection until no new declared binder is selected, with a finite
admission and work budget. Inconsistent selections fail; later iterations never
replace an earlier selection. A closed declared residual can supply further
member constraints, and keeps both its type witness and its independent row
selection. The shared row solver still validates the complete application.

Only the callee's own generic binders are inference variables. Captured types
and rows remain fixed or rigid. A row first mentioned by the callee can refer
to an outer declared Type binder; its local row ID does not make that outer
binder flexible. Exact caller residuals can forward their registered type
identity without being called closed. A same-declaration recursive application
cannot select a rigid caller member as a concrete type merely because its
spelling matches the callee's binder.

Evaluated preparation of a complete supported named-function Type argument
list resolves each explicit argument once in the caller, installs the selected
types and registered residuals, then checks the bounds. This allows an earlier
bound to refer to a later selected type. It does not change the separate
telescopic default preparation of type functions and type declarations.

The Windows gate in
`target/dependent-bound-and-entry-integration-windows-v2.log` passes all 32
focused application tests and five source groups, including both layouts/Core,
complete empty-array dimensions, actual callable labels/defaults, captured
rigidity, and returned-`U` Result producer transfer. Its full library gate has
425 passing tests and one pre-existing ignored test. The corresponding Linux
gate in `target/dependent-bound-static-linux-v3.log` passes the same library
and five new source groups, together with the preceding static regressions
(483 passing tests, one pre-existing ignored test). The new member fixture also
executes all six values on Windows and Linux, including scalar and nested
members, arrays, declared residuals, actual callable labels, and defaults. The
native results are recorded in
`target/optional-entry-bound-generic-native-windows-v1.log` and
`target/optional-entry-bound-generic-native-linux-v1.log`.

## Symbolic aliases and nested templates

Alias inference expands the declaration's structure with opaque placeholders
for registered binder identities. Selected closed callable syntax is kept out
of that structural expansion: labels, defaults, and invocation targets remain
in the selected source witness and actual value. A placeholder is private
inference metadata and cannot become a closed source witness. Unknown captured
alias meanings remain NI rather than being rebound by a matching local name.

Map key/value and callable parameter/result templates can supply complete child
constraints. Map lookup receives the declared key type and retains the Optional
shell around the complete value schema. Empty array dimensions and callable
modes still require their complete source syntax. Optional fallback receives
the payload type and joins the payload with the fallback; a diverging fallback
does not make a possibly present payload diverge.

Named callable signature queries install the definition's captured generic
environment and genuine binder IDs before resolving parameter and return
syntax. They do not reuse an unrelated caller's schema bindings. This repairs
the alias-wrapped callable regression in which a query saw `Box<T>` with an
empty binder registry. The observed diagnostic is recorded in
`target/static-symbolic-alias-wrapper-diagnostic-windows-v1.log`.

The focused repair gate in
`target/static-symbolic-alias-wrapper-fixed-windows-v2.log` passes 444 library
tests, with one pre-existing ignored test, and all ten static record-bound
Result source groups. It includes the original callable-wrapper fixture, a
complete Session/Core regression, and an empty-caller-scope signature test.

The completed v9 integration runs are recorded in
`target/scoped-write-template-integration-windows-v9.log` and
`target/scoped-write-template-integration-linux-v9.log`. Each platform passes
444 library tests and 146 source tests, with one pre-existing ignored library
test. The source gates include both static layouts/Core, the seven template
groups, the restored ten record-bound Result groups, and the fallback boundary
regressions.

Fresh v9 CLI/native execution also passes on both platforms. The template
fixture checks seven computed values, the dependent-member fixture six, and
the constructor fixture four; the record-bound Result executable also runs
all five programs, including the original callable-wrapper regression. Their
Windows logs use the stem `target/scoped-write-template-native-windows-v9-`
followed by `static-bound-template-inference`, `static-bound-generic-members`,
`static-bound-construction-contexts`, or `static-record-bound-results` and
`.log`. Linux logs use the corresponding stem
`target/scoped-write-template-native-linux-v9-` and underscore-separated test
names. The reports are
`target/scoped-write-template-native-windows-v9-results.json` and
`target/scoped-write-template-native-linux-v9-report.json`.

The complete native batch runs ten test executables on each host, covering 36
distinct positive source programs and 38 entry jobs. Each host's CLI, runtime,
and ten test-executable hashes are unchanged before and after execution. The
CLI SHA-256 values are
`234958D437DEA03B2FFA25AFA1EC34607041DE9CB141148A392C0E0A418A52BA`
on Windows and
`725054d1e8ff7fcc4361dc5b478cbd8df6c21a04e246d47fe4122befe2d70458`
on Linux. These results close this integration batch, not the remaining sorts,
proof boundaries, or full language corpus.

## Result contexts and the v21 integration

Named static applications now infer still-missing Type parameters from a full
written result context under its frozen lexical environment. Explicit and
input selections retain priority. An open caller type forwards its real binder
identity without acquiring a closed witness. The same context reaches ordinary
typing, complete source queries, evaluated preparation and the independent
Result-flow graph. Argument preparation and invocation share one real owner.

Declared dynamic return shells stay dynamic. Expected fixed dimensions,
callable modes, labels, defaults and immutable qualifications do not rewrite an
already selected argument or grant permission. Ordinary receiving still applies
an explicit callable view afterward. Optional lifting supplies only an Optional
type context, never a `Some` or inspection fact. Computed written dimensions use
their own static integer proof; aliases use only existing exact frozen instances
or the prior pure normalizer. A missing alias instance cannot interpret its
definition's free values in the caller.

The exact contract and remaining boundaries are documented in
`doc/STATIC_GENERIC_RESULT_CONTEXT_DESIGN.md`. The completed combined gates in
`target/static-result-context-and-structural-guards-integration-windows-v21.log`
and
`target/static-result-context-and-structural-guards-integration-linux-v21.log`
each pass 637 Rust tests across 21 targets (466 library and 171 Source tests),
with one pre-existing ignored library test. Both static layouts and positive
Core lowering are covered.

Fresh native execution is recorded in
`target/static-result-context-and-structural-guards-native-windows-v21-report.json`
and
`target/static-result-context-and-structural-guards-native-linux-v21-report.json`.
Each host passes 14 test executables with 19 Rust tests, 44 distinct positive
Ril sources and 48 entry jobs. CLI, runtime and all 14 test executable hashes
remain unchanged (16 artifacts per host). Scoped NI safety regressions remain
Source-only and are not counted as native or language acceptance.

## Scalar consts and the v30 checkpoint

Meta function `n: int` parameters have separate genuine value IDs. A universal
definition sees ordinary unknown `int`; a selected specialization records a
closed target-sized integer or forwards a real rigid caller const. The scalar
cannot become a Type binder, a closed object schema, or a proof about a Result
tag, freshness or escape. Missing values reject with `E0344`, wrong value sorts
with `E0323`, and target32 overflow cannot borrow the host's wider int range.

`BoundEnvironment` keeps visible const roles, ID history and immutable const
selections separately. A local/formal shadow installs a visible-role tombstone;
block, pattern, loop and callable boundaries restore their lexical roles along
with their value environments. The actual named-Meta path uses `enter_named`
and the existing value evaluation/sort checker, keeping older data/type/effect
float and aggregate const normalization intact. Signature checks use the
callee's captured lexical environment rather than a same-spelled caller value.

`const_argument_source` freezes a closed value into canonical literal syntax
and a rigid argument into its genuine internal binder ID. It does not reread a
later same-spelled local. Closed arguments need no captured scope; rigid ones
retain it. The frozen v25 first-class callable probe remains NI
(`static generic callable typing`), so the raw-name drift was a potential
internal proof gap, not an observed accepted unsafe program. Its before
evidence is retained in `target/static-const-captured-name-before-v25*`.

Scalar const dependencies in Type syntax are rejected as NI before complete
source/result-context normalization, even when an actual call selects a closed
`n`. No unknown `[n]T` is represented as dynamic `[]T`, and no backing count
infers `n`. Same-declaration unresolved const recursion also remains NI.

The v30 library includes eight new const identity/selection tests; the scalar
Source target passes six groups including pointer32/pointer64 checking and
Core lowering. Its one native fixture actually checks seven values
`2, -3, 9, 7, 6, 2, 4`, covering closed selection, forwarding, local shadowing,
nested capture, mixed Type/const parameters and a callee capture that shares a
name with the caller's const. The independent const Result-flow target passes
four Source groups and its native fixture computes 21 while preserving the
three original Result producers through block/pattern/loop shadows. The
unknown universal-branch case is a nonauthorization regression whose assertion
allows NI or `E0720`; it is not counted as a completed negative language case
merely because its Rust test passes.

The actual component logs are
`target/const-int-and-dependent-bound-full-source-windows-v30.log` and
`target/const-int-and-dependent-bound-full-source-linux-v30.log`: each contains
484 library and 195 Source passes across 25 targets, plus one explicit ignore.
The successful compiler all-target Clippy logs are
`target/const-int-and-dependent-bound-clippy-windows-v30.log` and
`target/const-int-and-dependent-bound-clippy-linux-v30.log`.

Fresh native reports are
`target/const-int-and-dependent-bound-native-windows-v30-report.json` and
`target/const-int-and-dependent-bound-native-linux-v30-report.json`. Each host
passes 17 test executables and 22 Rust tests, covering 49 distinct positive
sources and 53 executed entry jobs. CLI, runtime and all 17 test-executable
hashes remain unchanged before/after execution (19 artifacts). Earlier v28/v29
failed lint gates are not successful checkpoints. The subsequent v31 workspace
format check passes after formatting-only edits; it is not a new native build
or execution certificate.

## Remaining integration

The ordinary bound environment currently admits proved `Type`, structural
record and scalar `ConstInt` parameters. Concrete or computed row tails, broader value and
higher-kind arguments, and unresolved recursive interface summaries still need
their complete respective proofs. Composite open residual type selections and
an unannotated lambda return inferred from an expected callable still need
complete preparation. Scalar `n: int` Meta function generics are implemented;
dependent `[n]T` syntax, other Meta value sorts, static keys and higher kinds
remain NI. First-class generic callable Source typing also remains NI even
though its private const-argument canonicalization is implemented. Full static `Immut` expression evaluation is
separate from the already implemented transparent receiving-mask transport.

The independent static Result-flow graph now transports original producers
through its finite map lookup and container operations, as exercised by the v21
Source/model/native cases. An outer Optional presence check does not inspect a
nested Result. Unresolved map states or unsupported operations still need their
own transfer proofs; desired result types cannot make their values inspected,
absent or independently allocated.

The optional-fallback integration batch enforces the specified control
boundary: direct outward `return`, `last`, `next`, and propagation are `E0710`.
A nested callable owns its return target, and a loop created inside the fallback
owns its local `last`/`next` targets. Non-Option/Result operands are `E0714`,
and a raw Result fallback is `E0711`. An unresolved Result error-consumption
proof remains NI. Earlier acceptance of `value ?? { return 9 }` was an
implementation defect, not a positive language result; its source, frozen
test-executable hash, and observed acceptance log are preserved under
`target/static-coalescing-outward-return-before*` for the repair regression.

Source, Core, native, layout, and full-workspace gate results belong to their
actual integration reports. Focused type or evaluator tests alone do not claim
language conformance, native execution, or completion of the compiler.
