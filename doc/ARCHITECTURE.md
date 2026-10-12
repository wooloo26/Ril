# Compiler Architecture

Ril is a Rust workspace with native compilation as its first target and a shared
semantic boundary for future GC-language and other backends. SPEC.md and STD.md
remain the normative language contracts.

## Workspace organization

All ten application/library crates live under crates/. The eleventh workspace
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
    xtask --> corpus["ril-test"]
~~~

ril-ir depends only on ril-compiler-core. It does not depend on Rowan, Salsa,
the semantic checker or lowering implementations. ril-codegen provides backend
interfaces and target descriptions without depending on a concrete emitter.
ril-compiler uses these abstract interfaces; it does not depend on Cranelift.
Neither runtime crate depends on compiler, syntax or code-generation crates.
The corpus tool remains independent of the compiler.

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
inputs change. The current session models one source input; persistent caches,
watchers, language servers and package resolution are future work.

Session, CompilationOutcome, check_path and build_path are exported from the
ril-compiler crate root. CLI presentation is separate. Unimplemented phases use
the shared phase::Stage identities rather than empty per-phase modules.

## Native targets and runtime

The initial targets remain x86_64-pc-windows-msvc (COFF) and
x86_64-unknown-linux-gnu (ELF), both little-endian with 64-bit pointers. Target
properties are separate from implementation availability: an OS capability
does not imply an implemented Ril library operation.

Cranelift accepts an explicitly constructed native IR module with exported,
zero-argument functions returning an i64 constant. Tests emit both object
formats on either host and inspect their architectures and defined symbols.
This validates the emitter boundary; it is not a Ril source compilation or a
linked-program test. Cranelift types do not escape the concrete backend.

Object emission and platform linking have separate interfaces. LinkRequest
identifies objects, the target runtime library and output. The future linker
will invoke tools with argument vectors and distinguish missing tools,
unsupported combinations and link failures. The current CLI invokes no linker.

ril-runtime-api defines logical contracts, not a frozen binary ABI.
CONTRACT_VERSION is 1. Artifacts record runtime_contract_version, and native
runtime status exposes contract_version. Concrete binary layouts and calling
conventions will be defined together with runtime integration.

Explicit managed handles, type descriptors, roots, object tracing and safepoints
establish the collector boundary. Suspended computations and tasks must retain
their roots. Language panic is distinct from Rust panic and native crashes.
Scoped cleanup, cancellation and task completion preserve language semantics
independently of GC timing. The collector and scheduler are not implemented.

## Current capabilities and development

The workspace uses Rust 1.99.0, Edition 2024 and Cargo resolver 3, with external
dependencies pinned by Cargo.lock. Project implementation and maintenance logic
are Rust; TOML and CI YAML provide configuration. rustc, Git, system APIs and
platform linkers are external development/platform tools.

Implemented infrastructure includes byte-preserving source storage, structured
diagnostics, target descriptions, a lossless Rowan unparsed envelope, Salsa
source queries, the native object probe, and the complete corpus tool.

Ril lexing/parsing, semantic analysis, both lowering paths, linking, collection
and task scheduling remain unimplemented. check/build report that explicitly
and emit no executable artifacts. Invalid UTF-8 can already produce E0104;
this does not imply complete lexical conformance or semantic test execution.

~~~text
cargo build --workspace --locked
cargo run --locked -p ril-cli -- --help
cargo run --locked -p ril-cli -- targets
cargo xtask corpus validate
cargo xtask corpus list
cargo xtask corpus extract <case-id> --out <empty-directory>
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

A future executor must create fresh program state and a workspace for each
case, honor arguments/environment without shell evaluation, build declared
helpers, enforce timeouts and terminate child processes. Those execution
responsibilities are not part of the current container tool. Validation
continues to report semantic execution as not-run.

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
