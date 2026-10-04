# The Ril Language Specification

**Version:** 0.1.0-draft  
**Status:** Working Draft (Experimental / Unstable)  
**Target Audience:** Compiler Implementors, Tooling Authors, Language Verifiers  

---

## Abstract

This document constitutes the formal, canonical reference specification for the **Ril** programming language. It serves as the authoritative **Single Source of Truth (SSOT)** for all conforming Ril compiler implementations, interpreters, static analyzers, and runtime systems.

Ril is an expression-oriented, strongly typed, statically analyzed programming language featuring garbage collection, algebraic effect handlers, fine-grained state capability tracking, predicative universe polymorphism, dependent records, and zero-cost compile-time type computation. Ril is designed to compile deterministically to both native machine binaries and ECMAScript/JavaScript modules with first-class TypeScript declaration bindings (`.d.ts`), maintaining strictly identical numeric, semantic, and operational behaviors across all targets.

---

## 1. Conformance and Normative Language

The key words **"MUST"**, **"MUST NOT"**, **"REQUIRED"**, **"SHALL"**, **"SHALL NOT"**, **"SHOULD"**, **"SHOULD NOT"**, **"RECOMMENDED"**, **"NOT RECOMMENDED"**, **"MAY"**, and **"OPTIONAL"** in this specification are to be interpreted as described in [BCP 14](https://www.rfc-editor.org/info/bcp14) ([RFC 2119](https://www.rfc-editor.org/rfc/rfc2119.txt) and [RFC 8174](https://www.rfc-editor.org/rfc/rfc8174.txt)) when, and only when, they appear in all capitals.

### 1.1 Conformance Classes

A compiler or implementation is classified under the following formal criteria:

1. **Conforming Ril Compiler**: An implementation that accepts all syntactically and semantically valid Ril programs, rejects all invalid programs at compile time with normative static errors, and emits code that adheres strictly to the evaluation, memory, effect, and panic semantics defined herein.
2. **Conforming Native Backend**: A code-generation backend producing native machine code (via LLVM, Cranelift, C, or native assembly) matching the exact integer, floating-point, memory model, and cleanup semantics specified.
3. **Conforming JavaScript Backend**: A code-generation backend producing ECMAScript modules and accompanying TypeScript definitions adhering to the exact boundary conversion, integer range check, and Promise-mapping semantics specified in [§15 (Host Interoperability and ABI)](spec/15_host_interoperability_and_abi.md).

---

## 2. Specification Architecture and Table of Contents

The specification is organized into sixteen modular normative chapters and a formal grammar appendix:

| Chapter | Specification Document | Description |
| :--- | :--- | :--- |
| **01** | [Conformance and System Architecture](spec/01_conformance_and_architecture.md) | Scope, execution model, dual-target requirements, abstract machine, and panic semantics. |
| **02** | [Lexical Structure](spec/02_lexical_structure.md) | Unicode source text, comments, whitespace, identifiers, keywords, and literal tokens. |
| **03** | [Formal Grammar and Syntax](spec/03_formal_grammar_and_syntax.md) | EBNF grammar notation, operator precedence table (Levels 1–17), and expression boundaries. |
| **04** | [Types and Type System](spec/04_types_and_type_system.md) | Universes, definitional equality, subtyping, variance, row polymorphism, and generalization. |
| **05** | [Memory Model and Storage](spec/05_memory_model_and_storage.md) | Value vs. reference types, handle-level read-only invariant, definite mutation, aliasing, live views, `snapshot`, and `produce`. |
| **06** | [Declarations and Items](spec/06_declarations_and_items.md) | Module-level items, record schemas, sum types, indexed GADTs, nominal wrappers, and opaque types. |
| **07** | [Expressions and Operators](spec/07_expressions_and_operators.md) | Arithmetic, wrapping math, bitwise, relational, logical, range, indexing, pipelines (`\|>`, `!>`), `??`, `?`. |
| **08** | [Control Flow and Pattern Matching](spec/08_control_flow_and_patterns.md) | Blocks, `where` clauses, `if`, loops (`loop`, `while/else`, `for/else`), patterns, exhaustiveness, `is`. |
| **09** | [Functions and Callables](spec/09_functions_and_callables.md) | Signatures, parameters (`mut`, `erased`), defaults, named args, closures, higher-order functions, hoisting. |
| **10** | [Algebraic Effects and Handlers](spec/10_algebraic_effects_and_handlers.md) | Effect declarations, aliases, `with` handlers, `resume`, built-in `@Async`, `@Div`, `Fuel`, isolation. |
| **11** | [State and Capability Tracking](spec/11_state_and_capability_tracking.md) | Annotations `&mut`, `&^mut`, `&capture`, `&{var}`, `&{mut var}`, local mutation purity, and retained sharing. |
| **12** | [Type Computation and Proofs](spec/12_type_computation_and_proofs.md) | Halting functions (`halt fn`), structural induction, `match type`, `Eq`, `Refl`, rewriting, protocols. |
| **13** | [Error Handling and Resources](spec/13_error_handling_and_resources.md) | `Option<T>`, `Result<T, E>`, postfix `?`, `??` fallback rules, unused Result enforcement, `defer`, handles. |
| **14** | [Modules and Compilation Units](spec/14_modules_and_compilation_units.md) | Acyclic module DAG, `pub` visibility, zero side-effect top-level initialization, entry point `main`. |
| **15** | [Host Interoperability and ABI](spec/15_host_interoperability_and_abi.md) | `decl` contracts, `.d.ril` / `.ril.ts` boundaries, numeric/byte translations, and JS Promise mapping. |
| **16** | [Standard Prelude](spec/16_standard_prelude.md) | Built-in primitive types, constructors, collection types (`Map`, `Set`), and prelude functions. |
| **App** | [Appendix: Consolidated Formal EBNF Grammar](spec/appendix_ebnf_grammar.md) | Machine-readable, full Context-Free EBNF Grammar Specification for parser generation. |

---

## 3. Guiding Architectural Principles

Compiler implementors MUST evaluate design and implementation decisions against the following core tenets:

1. **Occam's Principle of Surface Semantics**: The language specification defines observable program behavior, type safety contracts, and reject/panic criteria. Compilers are free to perform optimizations (e.g., inlining, escape analysis, devirtualization, monomorphization) provided observable behavior is invariant.
2. **Determinism Across Targets**: No implementation-defined or undefined behavior (UB) exists in Ril. Numeric arithmetic, wrapping, floating-point rounding, overflow detection, and exception unwinding MUST produce identical outcomes on native CPUs and JavaScript runtimes.
3. **Zero Hidden State**: Mutable side effects are never invisible. In-place modification requires an explicit `let mut` root or `mut` parameter; external state captures require static capability annotations (`&{mut name}`); side-effecting operations require explicit algebraic effects (`@Effect`).
4. **Safety Against Fault Masking**: Fallible operations yielding `Result` cannot be silently discarded, ignored via wildcard patterns, or bypassed using uninspected fallback values without explicit closures.
