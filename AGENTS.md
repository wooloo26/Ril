# Repository guidance

## Editing restrictions

Do not modify `README.md` or `AGENTS.md` unless the user explicitly requests it.

## Git workflow

Work directly on `main` and commit changes there. Do not create, switch to, or
use other branches unless the user explicitly requests them.

## Project structure

| Path | Purpose |
| --- | --- |
| `README.md` | Language introduction and examples |
| `DEVELOPMENT.md` | Build/test workflow and current implementation gaps |
| `AXIOMS.md` | Semantic kernel invariants and completion roadmap |
| `doc/SPEC.md` | Normative language specification |
| `doc/STD.md` | Normative standard library specification |
| `crates/` | Compiler, backends, runtime and shared libraries |
| `tests/` | Ril corpus: conformance, diagnostics, standard library, integration, regressions, properties, fuzz, stress and performance |
| `xtask/` | Corpus runner, repository checks, Git hooks and Unicode generation |
| `.cargo/` | Cargo aliases and workspace command configuration |
| `.config/` | Test runner configuration |
| `.github/` | CI workflows |
| `Cargo.toml`, `Cargo.lock` | Workspace packages and pinned dependency resolution |
| `rust-toolchain.toml` | Pinned Rust toolchain and components |
| `target/`, `.local/` | Disposable build output and local scratch data |

## Crates

| Crate | Responsibility |
| --- | --- |
| `ril-compiler-core` | Source locations, typed IDs, diagnostics and phase outcomes |
| `ril-syntax` | Lexer, recovery parser, Rowan CST and source AST |
| `ril-compiler` | Modules, static evaluation, HIR, semantic analysis and Core lowering |
| `ril-ir` | Core/native IR and retained semantic evidence |
| `ril-codegen` | Backend/linker interfaces, targets and native lowering |
| `ril-codegen-cranelift` | Cranelift AOT object emission |
| `ril-runtime-api` | Runtime ABI and execution/heap contracts |
| `ril-runtime` | GC, continuations, resources, scheduling and standard operations |
| `ril-text-format` | Shared scalar formatting and output limits |
| `ril-cli` | Compiler commands, backend selection and provider configuration |
| `ril-test` | Corpus parsing, extraction and expected/observed outcomes |
