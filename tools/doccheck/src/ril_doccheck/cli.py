"""Command-line entry point for read-only repository documentation checks."""

import argparse
import sys
import tomllib
from collections.abc import Sequence
from pathlib import Path

from ril_doccheck.diagnostics import Diagnostic
from ril_doccheck.grammar import check_grammar
from ril_doccheck.markdown import Document, check_links, read_document

PROJECT = Path(__file__).resolve().parents[2]
_EXCLUDED = {"node_modules", "target", "dist", "build", "__pycache__"}


def find_root(start: Path) -> Path:
    for candidate in (start, *start.parents):
        if (candidate / "doc" / "SPEC.md").is_file():
            return candidate
    return start


def markdown_files(paths: Sequence[Path]) -> list[Path]:
    result: set[Path] = set()
    for path in paths:
        if not path.exists():
            raise FileNotFoundError(f"input does not exist: {path}")
        if path.is_file():
            if path.suffix.lower() != ".md":
                raise ValueError(f"input must be a Markdown file or directory: {path}")
            result.add(path.resolve())
        else:
            for directory, names, filenames in path.walk():
                names[:] = [
                    name for name in names if not name.startswith(".") and name not in _EXCLUDED
                ]
                result.update(
                    (directory / name).resolve()
                    for name in filenames
                    if Path(name).suffix.lower() == ".md"
                )
    return sorted(result)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check Markdown structure, local links and Ril EBNF."
    )
    parser.add_argument(
        "paths", nargs="*", type=Path, help="files/directories; default: repository"
    )
    parser.add_argument("--root", type=Path, help="repository root for /-relative local links")
    args = parser.parse_args(argv)
    root = args.root.resolve() if args.root else find_root(Path.cwd())
    paths = args.paths or [root]
    try:
        config = tomllib.loads((PROJECT / "pyproject.toml").read_text(encoding="utf-8"))["tool"][
            "ril-doccheck"
        ]
        selected = markdown_files(paths)
    except (OSError, ValueError) as error:
        print(f"ril-doccheck: {error}", file=sys.stderr)
        return 2
    if not selected:
        print("ril-doccheck: no Markdown files selected", file=sys.stderr)
        return 2
    documents: dict[Path, Document] = {}
    diagnostics: list[Diagnostic] = []
    for path in selected:
        try:
            document = read_document(path)
        except (OSError, UnicodeError) as error:
            diagnostics.append(
                Diagnostic(path, 1, 1, "IO001", f"cannot read UTF-8 document: {error}")
            )
            continue
        documents[path] = document
        diagnostics.extend(document.diagnostics)
    diagnostics.extend(check_links(documents, root))
    blocks = [block for document in documents.values() for block in document.blocks]
    diagnostics.extend(
        check_grammar(
            blocks,
            externals=frozenset(config.get("externals", {})),
            notation_sections=frozenset(config.get("notation-sections", [])),
        )
    )
    for diagnostic in sorted(diagnostics):
        print(diagnostic.render(root))
    grammar_count = sum(block.language == "ebnf" for block in blocks)
    print(
        f"Checked {len(selected)} Markdown files and {grammar_count} EBNF blocks; "
        f"{len(diagnostics)} errors."
    )
    return 1 if diagnostics else 0
