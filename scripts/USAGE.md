# Development scripts

Run the commands below from the repository root with uv and Python 3.13.

## Script quality checks

```sh
uv sync --directory scripts --locked
uv run --directory scripts --locked quality
uv run --directory scripts --locked pytest
```

`quality` runs Ruff formatting and lint checks, mypy, pytest, and `doc_check`.

## Documentation validation

```sh
uv run --directory scripts --locked doc_check
uv run --directory scripts --locked doc_check ../doc/SPEC.md
```

`doc_check` checks Markdown structure, local links, and Ril EBNF. It scans the
repository by default. Explicit paths are relative to `scripts/`, and the
selected files share an EBNF production namespace.

## Formal verification

With `lake` on `PATH`, run the Lean build, fixtures, and axiom audit.

```sh
uv run --directory scripts --locked formal_check
```

The runtime proofs cover finite execution prefixes, including prefixes of
diverging runs. See the [checker](../formal/RilAccess/Provenance/Kernel.lean)
and [machine proofs](../formal/RilAccess/Provenance/MachineProofs.lean).
