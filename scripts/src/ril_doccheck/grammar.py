"""Check EBNF syntax and references across the document set."""

import re
from collections.abc import Iterable
from dataclasses import dataclass
from functools import cache
from importlib.resources import files

from lark import Lark, Token, UnexpectedInput, UnexpectedToken

from ril_doccheck.diagnostics import Diagnostic
from ril_doccheck.markdown import CodeBlock

_PRODUCTION = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*)[ \t]*::=", re.MULTILINE)


@dataclass(frozen=True)
class Reference:
    name: str
    line: int
    column: int


@dataclass(frozen=True)
class Production:
    name: str
    block: CodeBlock
    line: int
    references: tuple[Reference, ...]


@cache
def _parser() -> Lark:
    grammar = files("ril_doccheck").joinpath("ebnf.lark").read_text(encoding="utf-8")
    return Lark(grammar, parser="lalr", propagate_positions=True)


def _position(block: CodeBlock, offset: int) -> tuple[int, int]:
    return block.line + block.content.count("\n", 0, offset), offset - block.content.rfind(
        "\n", 0, offset
    )


def parse_block(block: CodeBlock) -> tuple[list[Production], list[Diagnostic]]:
    productions: list[Production] = []
    diagnostics: list[Diagnostic] = []
    matches = list(_PRODUCTION.finditer(block.content))
    prefix = block.content[: matches[0].start()] if matches else block.content
    if prefix.strip() or not matches:
        diagnostics.append(
            Diagnostic(
                block.path, block.line, 1, "EBNF001", "expected a Name ::= expression production"
            )
        )
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(block.content)
        body = block.content[match.end() : end]
        line, _ = _position(block, match.start())
        try:
            tree = _parser().parse(body)
        except UnexpectedInput as error:
            at_end = isinstance(error, UnexpectedToken) and error.token.type == "$END"
            offset = (
                len(body)
                if at_end or error.line < 1
                else sum(len(line) for line in body.splitlines(keepends=True)[: error.line - 1])
                + error.column
                - 1
            )
            error_line, column = _position(block, match.end() + offset)
            diagnostics.append(
                Diagnostic(
                    block.path,
                    error_line,
                    column,
                    "EBNF001",
                    f"invalid EBNF in {match[1]}: expected a valid expression or delimiter",
                )
            )
            continue
        references: list[Reference] = []
        for node in tree.find_data("reference"):
            token = node.children[0]
            assert isinstance(token, Token)
            assert token.start_pos is not None
            ref_line, column = _position(block, match.end() + token.start_pos)
            references.append(Reference(str(token), ref_line, column))
        for node in tree.find_data("character_class"):
            token = node.children[0]
            assert isinstance(token, Token)
            try:
                re.compile(str(token))
            except re.error as error:
                assert token.start_pos is not None
                error_line, column = _position(block, match.end() + token.start_pos)
                diagnostics.append(
                    Diagnostic(block.path, error_line, column, "EBNF001", f"invalid class: {error}")
                )
        productions.append(Production(match[1], block, line, tuple(references)))
    return productions, diagnostics


def check_grammar(
    blocks: Iterable[CodeBlock],
    *,
    externals: frozenset[str] = frozenset(),
    notation_sections: frozenset[str] = frozenset(),
) -> list[Diagnostic]:
    diagnostics: list[Diagnostic] = []
    definitions: dict[str, Production] = {}
    productions: list[Production] = []
    for block in blocks:
        if block.language != "ebnf":
            continue
        parsed, errors = parse_block(block)
        diagnostics.extend(errors)
        if notation_sections.intersection(block.sections):
            continue
        productions.extend(parsed)
        for production in parsed:
            if production.name in definitions:
                previous = definitions[production.name]
                diagnostics.append(
                    Diagnostic(
                        block.path,
                        production.line,
                        1,
                        "EBNF002",
                        f"duplicate production {production.name} (first at "
                        f"{previous.block.path.name}:{previous.line})",
                    )
                )
            definitions[production.name] = production
    for production in productions:
        for reference in production.references:
            if reference.name not in definitions and reference.name not in externals:
                diagnostics.append(
                    Diagnostic(
                        production.block.path,
                        reference.line,
                        reference.column,
                        "EBNF003",
                        f"undefined nonterminal {reference.name} in {production.name}",
                    )
                )
    return diagnostics
