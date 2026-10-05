# 14. Modules and Compilation Units

This chapter specifies source files, the compilation unit model, module namespaces, dependency resolution, visibility rules, top-level purity invariants, and unit testing.

---

## 1. Compilation Units and Source Mapping

A Ril compilation unit corresponds either to a single physical source file (`.ril`) or a directory containing a titular source file (`foo/foo.ril` or `foo/mod.ril`).

---

## 2. Module Import Resolution (`use`)

```ebnf
ModulePath  ::= [ "./" | "../" { "../" } ] PathSegment { "/" Identifier }
UseItem     ::= Identifier [ "as" Identifier ]
UseItemList ::= UseItem { "," UseItem } [ "," ]
UseDecl     ::= [ "pub" ] "use" ModulePath [ "::" ( "*" | "{" UseItemList "}" | Identifier ) ] [ "as" Identifier ]
```

### 2.1 Resolution Hierarchy

1. **Relative Imports**: Paths beginning with `./` or `../` resolve relative to the directory containing the importing source file (e.g., `use ./utils`, `use ../models::{User, Account}`).
2. **Project-Root Relative Imports**: Paths beginning with a project-level folder name (such as `src/`) resolve relative to the project root directory identified by `ril.toml`.
3. **Standard Library Imports**: Paths beginning with `ril/` resolve to the built-in Ril standard library modules (e.g., `use ril/io::{println}`, `use ril/str`).
4. **Aliasing and Selective Imports**:
   - `use ril/io::{read as rd}` renames the imported symbol.
   - `pub use path::*` re-exports all public symbols of the target module.

### 2.2 Strict Module DAG Invariant

> **Normative Rule**: The module dependency graph of a Ril program **MUST form a Directed Acyclic Graph (DAG)**.

Cyclic module dependencies (e.g., module `A` imports module `B` while module `B` directly or transitively imports module `A`) are **strictly PROHIBITED** and MUST be rejected at compile time.

### 2.3 Scoped Imports (Block-Scoped `use`)

A `use` declaration MAY appear within any statement block (`Block`), including function bodies, conditional branches, or loop bodies.

1. **Lexical Confinement**: Symbols introduced by a block-scoped `use` declaration are visible ONLY from the point of declaration to the closing delimiter `}` of that enclosing block. They MUST NOT leak into enclosing or sibling scopes.
2. **Shadowing**: A block-scoped `use` declaration shadows any identical symbol previously visible from outer module scopes or the standard prelude within that block.
3. **Export Prohibition (`InvalidPublicScopeError`)**: A `use` declaration situated inside a block MUST NOT include the `pub` modifier. Marking a block-scoped import as `pub` is a compile-time static error (`InvalidPublicScopeError`).
4. **Ergonomic Pipeline Imports**: Block-scoped imports enable localized access to domain-specific or container mutation functions (such as `push` or `pop`) without polluting the outer or global namespace:
   ```ril
   fn build_records(items: []int) -> []int {
       use ril/array::{push} -- Localized import: visible only within build_records
       let mut result = []
       for items as item {
           result !> push(item * 2)
       }
       result
   }
   ```

---

## 3. Top-Level Zero Side-Effect Initialization

> **Normative Rule**: Top-level module item initializers (`let` and `pub let` bindings) **MUST be strictly pure expressions**.

1. Invoking algebraic effects (`@Effect`), mutating external variables, or performing input/output (I/O) inside a top-level initializer is a compile-time static error.
2. All runtime side effects, initialization routines, and setup procedures MUST execute within functions (such as `pub fn main`) or inside `test` blocks.

---

## 4. Block-Scoped Modules

Modules MAY also be declared directly within source files using block syntax:

```ebnf
ModuleDecl ::= [ "pub" ] "module" Identifier "{" { Separator } [ Item { Separators Item } [ Separators ] ] "}"
```

```ril
module state {
    pub let max_capacity = 100
    let mut current_load = 0 -- valid: private module-scoped mutable variable
    
    pub fn record_load() &{mut current_load} {
        current_load += 1
    }
}
```

### 4.1 Visibility Rules (`pub` vs. Private)

1. Items are private to their declaring module by default.
2. Marking an item with `pub` exports it to parent and importing modules.
3. Accessing a parent module scope from an inner block module uses the contextual prefix `super` (e.g., `use super::config_val`).

### 4.2 Module-Level Mutable Export Prohibition

Exporting a mutable module-level binding (`pub let mut`) across module boundaries is **strictly PROHIBITED** and MUST be rejected at compile time. Cross-module mutable state MUST be mediated via algebraic effects, parameter passing, or encapsulated capability closures (`&capture`).

---

## 5. Program Entry Point (`pub fn main`)

A standalone executable program begins execution at `pub fn main`:

```ril
pub fn main(args: []str = []) -> Result<(), str> @Io {
    println("Hello, Ril!")
    Ok(())
}
```

1. The entry function accepts an optional argument slice `args: []str = []`.
2. Standard unhandled effects declared on `main` (such as `@Io`) are discharged by the platform's host runtime environment.

---

## 6. Unit Testing (`test`)

Ril features first-class unit test declarations directly within source files:

```ebnf
TestDecl ::= "test" StringLiteral Block
```

```ril
fn add(a: int, b: int) -> int { a + b }

test "addition correctness" {
    assert((2 |> add(3)) == 5)
}
```

1. A `test` declaration associates an arbitrary descriptive string literal with an executable test block.
2. Test blocks possess permission to perform assertions (`assert(...)`) and execute setup side effects.
3. In production compilation modes, `test` blocks are completely eliminated from binary generation and carry zero runtime overhead.
