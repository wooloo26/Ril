# The Ril Language Specification

**Version:** 0.1.0-draft  
**Status:** Working Draft (Experimental / Unstable)  
**Target Audience:** Compiler Implementors, Tooling Authors, Language Verifiers  

---

## Abstract

This document constitutes the formal, canonical reference specification for the **Ril** programming language. It serves as the authoritative, canonical specification for all conforming Ril compiler implementations, interpreters, static analyzers, and runtime systems.

Ril is an expression-oriented, strongly typed, statically analyzed programming language featuring garbage collection, algebraic effect handlers, fine-grained state capability tracking, predicative universe polymorphism, dependent records, and compile-time type computation with zero runtime representation overhead. Ril compiles deterministically to native machine binaries, maintaining strictly deterministic numeric, semantic, and operational behaviors.

---

## 1. Conformance and Normative Language

The key words **"MUST"**, **"MUST NOT"**, **"REQUIRED"**, **"SHALL"**, **"SHALL NOT"**, **"SHOULD"**, **"SHOULD NOT"**, **"RECOMMENDED"**, **"NOT RECOMMENDED"**, **"MAY"**, and **"OPTIONAL"** in this specification are to be interpreted as described in [BCP 14](https://www.rfc-editor.org/info/bcp14) ([RFC 2119](https://www.rfc-editor.org/rfc/rfc2119.txt) and [RFC 8174](https://www.rfc-editor.org/rfc/rfc8174.txt)) when, and only when, they appear in all capitals.

### 1.1 Conformance Classes

A software system SHALL be classified under the following formal conformance criteria:

1. **Conforming Ril Compiler**: An implementation that MUST accept all syntactically and semantically valid Ril programs, MUST reject all invalid programs at compile time with normative static errors, and MUST emit artifacts adhering strictly to the operational, memory, effect, and panic semantics defined herein.
2. **Conforming Native Backend**: A code-generation backend that MUST produce native machine code (via LLVM, Cranelift, C, or native machine instructions) adhering to the exact integer, floating-point, memory model, and cleanup semantics specified herein.

---

## 2. Specification Architecture and Table of Contents

The specification is organized into seventeen modular normative chapters and a formal grammar appendix:

| Chapter | Specification Document | Description |
| :--- | :--- | :--- |
| **01** | [Conformance and System Architecture](spec/01_conformance_and_architecture.md) | Scope, execution model, native target requirements, abstract machine, and panic semantics. |
| **02** | [Lexical Structure](spec/02_lexical_structure.md) | Unicode source text, comments, whitespace, identifiers, keywords, and literal tokens. |
| **03** | [Formal Grammar and Syntax](spec/03_formal_grammar_and_syntax.md) | EBNF grammar notation, operator precedence table (Levels 1–17), and expression boundaries. |
| **04** | [Types and Type System](spec/04_types_and_type_system.md) | Universes, definitional equality, subtyping, variance, row polymorphism, and generalization. |
| **05** | [Memory Model and Storage](spec/05_memory_model_and_storage.md) | Value vs. reference types, handle-level read-only invariant, definite mutation, aliasing, live views, `clone`, `clone_immut`, and `produce`. |
| **06** | [Declarations and Items](spec/06_declarations_and_items.md) | Module-level items, record schemas, sum types, indexed GADTs, nominal wrappers, and opaque types. |
| **07** | [Expressions and Operators](spec/07_expressions_and_operators.md) | Arithmetic, wrapping math, bitwise, relational, logical, range, indexing, pipelines (`\|>`, `!>`), `??`, `?`. |
| **08** | [Control Flow and Pattern Matching](spec/08_control_flow_and_patterns.md) | Blocks, `where` clauses, `if`, loops (`loop`, `while`, `for`), patterns, exhaustiveness, `is`. |
| **09** | [Functions and Callables](spec/09_functions_and_callables.md) | Signatures, parameters (`mut`, `erased`), defaults, named args, closures, higher-order functions, hoisting. |
| **10** | [Algebraic Effects and Handlers](spec/10_algebraic_effects_and_handlers.md) | Effect declarations, aliases, `with` handlers, `resume`, built-in `@Async`, `@Div`, `Fuel`, isolation. |
| **11** | [State and Capability Tracking](spec/11_state_and_capability_tracking.md) | Annotations `&mut`, `&^mut`, `&capture`, `&{var}`, `&{mut var}`, `&{^mut var}`, local mutation purity, and origin-tracked retained sharing. |
| **12** | [Type Computation and Proofs](spec/12_type_computation_and_proofs.md) | Halting functions (`halt fn`), structural induction, `match type`, `Eq`, `Refl`, rewriting, protocols. |
| **13** | [Error Handling and Resources](spec/13_error_handling_and_resources.md) | `Option<T>`, `Result<T, E>`, postfix `?`, `??` fallback rules, unused Result enforcement, scoped resources (`let scoped`), handles. |
| **14** | [Modules and Compilation Units](spec/14_modules_and_compilation_units.md) | Acyclic module DAG, `pub` visibility, zero side-effect top-level initialization, entry point `main`. |
| **15** | [Host Interoperability and ABI (Reserved)](spec/15_host_interoperability_and_abi.md) | Reserved for future host interop, foreign function interface (FFI), and external ABI specifications. |
| **16** | [Standard Prelude](spec/16_standard_prelude.md) | Built-in primitive types, constructors, collection types (`Map`, `Set`), and prelude functions. |
| **17** | [Multicore Parallelism and Data Parallelism](spec/17_multicore_parallelism.md) | Work-stealing scheduling, local mutation purity dividend, data parallel pipelines (`par_map`, `par_fold`), structured task parallelism via multi-core nursery, and deterministic reduction. |
| **App** | [Appendix: Consolidated Formal EBNF Grammar](spec/appendix_ebnf_grammar.md) | Machine-readable, full Context-Free EBNF Grammar Specification for parser generation. |
| **Rat** | [Design Rationale and Defensive Principles](spec/DESIGN_RATIONALE.md) | Non-normative companion documenting architectural rationale, safety philosophy, and comparative language analysis. |

---

## 3. Guiding Architectural Principles
 
Compiler implementors MUST evaluate design and implementation decisions against the following core tenets:

1. **Occam's Principle of Surface Semantics**: The language specification defines observable program behavior, type safety contracts, and reject/panic criteria. A conforming compiler MAY perform optimizations (such as inlining, escape analysis, devirtualization, and monomorphization), provided that observable program behavior remains strictly invariant.
2. **Determinism**: A conforming Ril implementation SHALL NOT exhibit implementation-defined behavior or undefined behavior (UB). Numeric arithmetic, wrapping, floating-point rounding, overflow detection, and exception unwinding MUST produce identical, strictly deterministic outcomes.
3. **Zero Hidden State**: Mutable side effects are never invisible. In-place modification strictly requires an explicit `let mut` root or `mut` parameter; external mutable access requires `&{mut name}`, and retained writable sharing of a known external origin requires `&{^mut name}`; side-effecting operations strictly require explicit algebraic effects (`@Effect`). Interface abstraction MUST preserve any retained-sharing hazard.
4. **Safety Against Fault Masking**: Fallible operations yielding `Result` MUST NOT be silently discarded, MUST NOT be ignored via wildcard patterns, and MUST NOT be bypassed using uninspected fallback values without explicit closures.
