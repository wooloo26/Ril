# Compiler Architecture

Ril is a Rust workspace with native compilation as its first target and a shared
semantic boundary for future GC-language and other backends. SPEC.md and STD.md
remain the normative language contracts.

## Workspace organization

All eleven application/library crates live under crates/. The twelfth workspace
package, xtask, owns repository maintenance. tests/ contains only the existing
Ril language-test containers. A crate marks a dependency or reuse boundary;
closely related phases are modules inside the owning crate.

| Crate | Responsibility and modules |
| --- | --- |
| ril-compiler-core | Shared source bytes, spans, diagnostics, semantic identities and stage outcomes: source, diagnostic, ids, phase |
| ril-syntax | Rowan CST, typed AST access and parsing entry: syntax_kind, tree, ast, parse |
| ril-compiler | Shared frontend and orchestration: hir, sema, db, session, driver, lower |
| ril-ir | Data-only structured Core IR and native IR: core, native |
| ril-codegen | Abstract code generation: backend, target, artifact, link, lower |
| ril-codegen-cranelift | Cranelift AOT emission behind the native backend interface |
| ril-runtime-api | Logical managed-heap and execution contracts: gc, execution, error |
| ril-runtime | Native runtime implementation and availability |
| ril-text-format | Pure scalar formatting shared by static evaluation and runtime; explicit target int bounds and output budgets |
| ril-cli | The ril command-line application |
| ril-test | Test-container parsing, corpus validation, extraction and adapter contracts |
| xtask | Development commands and workspace architecture validation |

Each library root declares modules and exports its intended entry points.
The shared compiler core contains data needed by multiple phases, not a parser,
solver, query engine, runtime or general-purpose utilities collection.
DefinitionId, TypeId and OriginId live here so IR consumers do not depend on
semantic-analysis implementations.

The organization draws on these Rust implementations:

- [Gleam's compiler core](https://github.com/gleam-lang/gleam/blob/main/compiler-core/src/lib.rs)
  groups related analysis, parsing and source-generation functionality into
  modules. Ril similarly keeps closely related frontend phases together.
- [RustPython's compiler core](https://github.com/RustPython/RustPython/blob/main/crates/compiler-core/src/lib.rs)
  exposes common compilation data separately from its
  [compilation entry point](https://github.com/RustPython/RustPython/blob/main/crates/compiler/Cargo.toml).
  Ril separates reusable data from analysis and lowering.
- [rustc's backend interface](https://github.com/rust-lang/rust/blob/master/compiler/rustc_codegen_ssa/src/traits/backend.rs)
  separates code-generation contracts from concrete emitters. Ril keeps its
  emitter-specific types inside the corresponding backend crate.

These references inform boundaries; Ril's effects, provenance rules, tracing GC
and structured Core IR determine its own compiler design.

## Dependency direction

The following diagram shows workspace dependencies, not execution order:

~~~mermaid
flowchart TD
    cli["ril-cli"] --> compiler["ril-compiler"]
    cli --> codegen["ril-codegen"]
    compiler --> syntax["ril-syntax"]
    compiler --> ir["ril-ir"]
    compiler --> codegen
    compiler --> core["ril-compiler-core"]
    syntax --> core
    ir --> core
    codegen --> core
    codegen --> ir
    native["ril-codegen-cranelift"] --> codegen
    native --> ir
    native --> api["ril-runtime-api"]
    runtime["ril-runtime"] --> api
    compiler --> format["ril-text-format"]
    syntax --> format
    runtime --> format
    xtask --> corpus["ril-test"]
~~~

ril-ir depends only on ril-compiler-core. It does not depend on Rowan, Salsa,
the semantic checker or lowering implementations. ril-codegen provides backend
interfaces and target descriptions without depending on a concrete emitter.
ril-compiler uses these abstract interfaces; it does not depend on Cranelift.
Neither runtime crate depends on compiler, syntax or code-generation crates.
The corpus tool remains independent of the compiler.

`ril-text-format` has no workspace dependencies. It accepts ordinary scalar
values, a target pointer width and an explicit implementation output budget.
It shares Ril conversion rules without coupling the runtime to compiler data
or coupling compile-time execution to heap handles and native ABI state.

cargo xtask ci checks these boundaries using Cargo's resolved dependency graph
with all features and targets included. It checks production and build
dependencies, including transitive dependencies through external helpers;
dev-only edges are exempt. Workspace packages have explicit permitted internal
dependencies. Introducing a new package requires assigning it an architecture
policy. Backend implementations may use code-generation interfaces, IR, shared
compiler data and the runtime API, but not the frontend or query engine.

The native emitter can therefore build without compiling the Ril parser or
checker. Future source emitters can consume Core IR without bringing in
Cranelift or the native runtime implementation.

## Frontend, data and lowering

~~~text
source bytes -> lexer/CST/AST -> resolved HIR -> verified HIR
                                                    |
                                  ril-compiler::lower::lower_core
                                                    |
                                             structured Core IR
                                               /           \
                         ril-codegen::lower::lower_native   source backend
                                        |                        |
                                    native IR             GC-language source
                                        |
                              Cranelift -> COFF/ELF
                                        |
                            platform linker + native runtime
~~~

Semantic acceptance belongs to ril-compiler. It must enforce the specified
conservative rules for types, effects, origins, write authority, capture,
retained sharing, escape, termination and static evaluation. Annotations do not
manufacture authority or erase facts. Stable identities and diagnostic cause
graphs preserve source-to-use explanations independently of presentation.

VerifiedProgram is owned by ril-compiler::hir and has no public constructor.
The normal lowering path accepts this verification result. Core IR is ordinary
data with public construction; constructing it does not certify that a Ril
program passed semantic checking. This permits independent IR consumers and
explicit low-level backend tests without exposing a semantic-verification
constructor.

Core IR retains structured control, symbolic generic parameters, managed
references, source locations and provenance, effect operations, resumption and
cleanup. The current structures establish these boundaries, not a complete
instruction set. Extend them alongside language features and their tests.

HIR-to-Core lowering belongs to the compiler. Core-to-native lowering belongs
to code generation and owns monomorphization, closure environments,
effect/resumption representation, roots and safepoints, memory layout and
calling conventions. These representations must not leak into shared semantic
data. SourceBackend consumes Core IR before native lowering; each target must
preserve Ril arithmetic, evaluation order, identity, effects and cleanup.

Salsa is confined to ril-compiler::db. The driver performs filesystem I/O and
target selection outside queries; sessions supply source revisions to the
database. Queries derive deterministic facts and reuse results until their
inputs change. Session accepts either one source or an in-memory project with
stable per-file inputs and explicit add, edit, and remove operations. The
filesystem driver discovers modules outside queries. Persistent caches,
watchers, language servers and package resolution remain future work.

Session, CompilationOutcome, check_path and build_path are exported from the
ril-compiler crate root. CLI presentation is separate. Unimplemented phases use
the shared phase::Stage identities rather than empty per-phase modules.

## Native targets and runtime

The initial targets remain x86_64-pc-windows-msvc (COFF) and
x86_64-unknown-linux-gnu (ELF), both little-endian with 64-bit pointers. Target
properties are separate from implementation availability: an OS capability
does not imply an implemented Ril library operation.

Cranelift emits managed native functions and structured control flow from Core.
Closures use a uniform C ABI of environment and argument-tuple handles to a
result handle. Intermediate values and captured binding cells have explicit
roots. Tests compile, link and execute actual Ril sources on the host; separate
object-format tests inspect COFF and ELF output. Cranelift types do not escape
the concrete backend. Uniform boxed execution retains verified generic binder
identities; operations requiring unresolved specialization are unavailable.

Object emission and platform linking have separate interfaces. LinkRequest
identifies objects, the target runtime library and output. The system linker
uses argument vectors, discovers MSVC/SDK libraries on Windows and invokes cc
on Linux. Missing tools and unsupported cross-linking remain distinct from
link failures. CLI build/test inject the backend, linker and runtime library.

ril-runtime-api defines logical contracts and versioned native operation tags.
CONTRACT_VERSION is 3. Artifacts record runtime_contract_version, and native
runtime status exposes contract_version. Exported C functions pass only scalar
POD values, generation handles and explicit buffer pointers/lengths. The
availability table is exact: an unimplemented builtin cannot silently become
a native call that fails only at runtime.

Explicit managed handles, type descriptors, roots, object tracing and safepoints
establish the collector boundary. The non-moving mark-sweep heap preserves
cycles and internal aliases during deep clone; generation checks reject stale
handles. Scoped cleanup invokes current callbacks in LIFO order, with explicit
primary and cleanup fault causes, independently of collection. Language panic
is distinct from Rust panic and native crashes. Native continuation steps,
resumptions, delimiter/handler chains and captured cells are precisely traced.
Task actions, results, scope state and channel queues also retain their roots.
Execution state remains worker-local. An opt-in shared heap
serializes managed access at ABI safepoints and publishes each worker's precise
roots before releasing the gate. Infrastructure tests cover four allocating
workers collecting shared cycles, native callback reentry, and suspended
trampoline roots. Standard streams, sleep, entropy, process operations, file
stream operations and implicit file/child cleanup now separate request
preparation, host work and managed result construction. The host work runs
outside this gate. Child waits and sleep use wakeable task cancellation tokens;
cancelling a child wait preserves its owner's cleanup authority. Standard-stream
and file transfers use cancellable host requests; interruptible filesystem waits
have platform-specific cancellation workers. Source Concurrent scopes/tasks and
bounded channels execute through this shared heap. Ordinary tasks currently own
native threads, while Parallel uses bounded workers per operation. A bounded
task/IO executor and complete cancellation-exit semantic transport remain work in
progress. Platform interruption limits are documented in NATIVE_FILESYSTEM.md.

Effect operations carry verified identities into Core. Selective CPS uses a
transitive call-graph fixed point and conservatively includes dynamic calls.
The CPS native IR is a graph of ANF blocks; Cranelift emits each continuation
as machine code and a runtime trampoline dispatches steps outside heap borrows.
Tail resumption restores the request's handler chain; an arm runs outside its
selected handler, and abort bypasses the suspended body. GC-traced logical
activations retain scoped actions across physical native steps. Delimiter
checkpoints distinguish normal return from abort; deferred arm activations stay
alive until the resumed body completes, including on panic. Source tests execute
5,000 effect requests with shared mutable cells and collection, and verify LIFO
cleanup on suspension, abort, return, loop control, and resumed-body panic.
The task-owned cleanup outcome machine retains pending work and masks across CPS
invocations, including handlers entered during cleanup. See NATIVE_CLEANUP.md for
the ABI and fault-order contract. Retained handlers carry lexical definition and
callable-owner identities into reusable native recipes. The source solver delays
non-tail suffixes until the actual body answer and cleanup boundary, retaining
typed ordering evidence in Core. Checked copy answers and certified strict
identity transport of ordinary references/Results have native tests; richer
suffix and resource-answer proofs remain incomplete.

The runtime implements exact timestamp arithmetic, process-local monotonic
observations, SplitMix64 state, and host cryptographic entropy without seeded
fallback. Blocking time and entropy operations currently execute outside the
managed heap gate on the owning thread. Sleep is wakeable by task cancellation;
the host entropy operation has no general interruption guarantee. Runtime
availability and semantic permission contracts remain separate.

Native strings preserve raw POSIX bytes or Windows UTF-16 units. Paths use target
lexical rules without filesystem observations. File authorities use opaque,
nonclonable identities, shared open/position state, explicit close and a separate
finite implicit release. Rename uses atomic no-replacement platform operations;
it never checks existence then performs an overwriting rename. Environment
snapshots preserve native arguments and names. Host operations separate managed
request preparation/result construction from blocking work and preserve actual
partial-transfer outcomes on cancellation. A blocked native task is not yet a
parked continuation in a bounded scheduler.

Runtime unsafe exceptions are restricted to ABI calls and the small
`platform_file`, `platform_environment`, `platform_io`, `platform_stdio`, and
`platform_signal` modules. Each raw operation documents
ownership, buffer lifetime and host guarantees; the rest of the runtime retains
crate-level `deny(unsafe_code)` and compiler crates retain `forbid`.

## Current capabilities and development

The workspace uses Rust 1.99.0, Edition 2024 and Cargo resolver 3, with external
dependencies pinned by Cargo.lock. Project implementation and maintenance logic
are Rust; TOML and CI YAML provide configuration. rustc, Git, system APIs and
platform linkers are external development/platform tools.

Implemented paths include recovering lossless lexing/parsing, owned ASTs,
module resolution, type and capability checking, pure static evaluation,
termination obligations, verified HIR-to-Core lowering, managed native object
emission, linking, execution and the subprocess corpus adapter. Capability
evidence includes finite heap shapes, permission roots, conditional relations,
recursive summaries, Result duties and derivation causes; it crosses into Core
without granting authority to manually constructed IR.

This is an implementation in progress. Algebraic handlers/resumption,
comprehensive narrowing, resource contracts, concurrency, all static type
computation and the complete standard library are not yet fully covered.
check/build distinguish verified success, rejection and explicit unimplemented
features. Partial support and infrastructure tests do not establish complete
language conformance.

~~~text
cargo build --workspace --locked
cargo run --locked -p ril-cli -- --help
cargo run --locked -p ril-cli -- targets
cargo xtask corpus validate
cargo xtask corpus list
cargo xtask corpus extract <case-id> --out <empty-directory>
cargo xtask corpus run --mode check-pass --mode check-fail
cargo xtask corpus run --filter permissions --json
cargo xtask ci
~~~

Install cargo-nextest 0.9.148 using Cargo's --locked option before running ci.
The CI task checks architecture, formatting, Clippy, workspace builds, nextest,
doctests and corpus validity on Windows and Linux. Its child Cargo commands use
a separate target subdirectory so a Windows workspace build never replaces the
running xtask executable.

## Language-test contracts

Containers retain their --@ framing and five modes. Framing is independent of
embedded Ril syntax: malformed strings/comments cannot absorb following cases.
Text blocks materialize LF; hex blocks preserve arbitrary bytes, CRLF, invalid
UTF-8 and absent final newlines. Expectation-comment recognition handles nested
comments and interpolation independently.

The corpus contains 84 bundles, 1,067 cases, 176 diagnostic codes and 811 companion
links. Mode counts are 342 check-pass, 369 check-fail, 296 run-pass, 52 run-panic
and 8 run-program. Validation reads specification anchors and diagnostic
coverage directly, without a second specification registry.

The JSON form of corpus list exposes cases, inventory and expected outcomes.
CompilerAdapter is an internal Rust interface, not a compiler wire protocol.
Its facts distinguish static results, builds, runtime classification, panic
origin and exact output bytes. Diagnostics cannot be inferred from stderr, or
panic identity from an exit code. Warnings do not alter acceptance. Empty
selection, unimplemented stages and unavailable environments remain incomplete;
crashes and timeouts cannot satisfy expected language failures.

The executor creates fresh program state and an isolated workspace for each
case, honors arguments/environment without shell evaluation, builds declared
helpers, enforces timeouts and terminates child process groups or Windows Job
Objects. CLI JSON conveys diagnostics and runtime reports independently from
program output bytes. Run supports exact IDs, substrings, modes and an external
compiler path. Structural validation remains a separate command and continues
to label semantic execution as not-run; only actual execution can pass cases.
`--applicable-only` excludes runtime cases requiring the other known host OS,
records every exclusion separately, and leaves all static-layout cases selected.
Unknown capabilities and unavailable tools remain incomplete. The CI matrix
uses this flag; its selection union must still cover the full corpus.

## Implementation sequence

1. Implement recovering lexing/parsing and typed AST access.
2. Implement HIR resolution, type checking and the complete semantic fact graph.
3. Add static evaluation, termination checks and verified HIR-to-Core lowering.
4. Implement native representations, tracing GC, effects, cleanup and runtime
   operations alongside their conformance tests.
5. Link/run native programs and connect the real test adapter.
6. Add GC-language or other backends against the same verified semantics.

Add real phase modules and backend crates when their implementations need them.
Tooling tests and artificial IR probes do not count as language-conformance
executions.
