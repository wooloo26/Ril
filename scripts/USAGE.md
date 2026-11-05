# Development scripts

`scripts/` is the shared uv project for repository utilities that are easier to
write as scripts. Python 3.13 is selected in `.python-version` and dependencies
are pinned in `uv.lock`.

## Script quality checks

Run from the repository root:

```sh
uv sync --directory scripts --locked
uv run --directory scripts --locked quality
```

The quality command runs Ruff formatting checks, Ruff lint, strict mypy, pytest,
and documentation validation. Each check runs with this project as its working
directory, so its caches stay here. It reports all failed checks and exits nonzero.

Run individual checks from the repository root:

```sh
uv run --directory scripts --locked ril-doccheck
uv run --directory scripts --locked ruff check .
uv run --directory scripts --locked ruff format --check .
uv run --directory scripts --locked mypy
uv run --directory scripts --locked pytest
```

To format Python files, run `uv run --directory scripts ruff format .`.
To update locked dependencies, run `uv lock --directory scripts --upgrade`.

## Formal verification

With `lake` on `PATH`, run this command from the repository root.

```sh
uv run --directory scripts --locked python check_formal.py
```

The runner builds the Lean project in [`formal/`](../formal/lakefile.toml), checks
its examples, and audits project declarations. Lake keeps its build products
under `formal/.lake/`. The runner also works with `python3 scripts/check_formal.py`.

## Documentation validation

The default scope is all Markdown in the repository, excluding hidden and common
generated directories. Explicit input paths are relative to the working directory
(`scripts/` with the commands above). For example:

```sh
uv run --directory scripts --locked ril-doccheck ../doc/SPEC.md
```

Markdown is parsed structurally, including tables and strikethrough. Checks cover
heading-level jumps, unclosed or unlabelled code fences, and local links/images.
Heading anchors use GitHub-style lowercasing, punctuation removal, Unicode
letters/numbers/marks, and duplicate suffixes; explicit HTML IDs and named anchors
are also recognized. Remote URLs are skipped. Link locations identify the
containing Markdown block; EBNF columns are relative to the extracted code.

EBNF blocks share a production namespace across the selected files. Checks cover
malformed productions, unbalanced delimiters, invalid lexical ranges, duplicate
definitions and undefined nonterminal references, including forward references
between blocks. Quoted terminals are literal spellings, including SPEC's quoted
single backslash. Compact character classes containing ranges, negation or
escapes are recognized; `[Name]` and `[ Name ]` remain optional references.

The `Grammar Notation` section is syntax-checked as explanatory notation without
exporting its schematic productions or resolving its metavariables. The small,
documented list of prose-defined lexical names and the notation-section setting
live in `[tool.ril-doccheck]` in `pyproject.toml`; unknown names are never silently
accepted. Selecting only part of the grammar can report references defined in
unselected files.

These checks do not execute Ril examples or prove grammar unambiguity, operator
precedence, typing, access modes, effects or other semantic conformance rules.

Diagnostics use `path:line:column: CODE message`. Exit status is 0 for success,
1 for validation errors, and 2 for invalid input or invocation.
