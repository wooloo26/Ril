"""Parse Markdown once, retaining source locations for structural checks."""

import unicodedata
from dataclasses import dataclass
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit

from markdown_it import MarkdownIt
from markdown_it.token import Token

from doc_check.diagnostics import Diagnostic


@dataclass(frozen=True)
class CodeBlock:
    path: Path
    line: int
    language: str
    content: str
    sections: tuple[str, ...]


@dataclass(frozen=True)
class Link:
    target: str
    line: int


@dataclass(frozen=True)
class Document:
    path: Path
    anchors: frozenset[str]
    links: tuple[Link, ...]
    blocks: tuple[CodeBlock, ...]
    diagnostics: tuple[Diagnostic, ...]


class _Anchors(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.values: set[str] = set()

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        for key, value in attrs:
            if value is not None and (key == "id" or (tag == "a" and key == "name")):
                self.values.add(value)


def _heading_anchor(text: str, used: set[str]) -> str:
    # GitHub-style anchors: retain Unicode letters/numbers/marks, hyphens and
    # underscores; remove punctuation/symbols, then replace spaces with hyphens.
    base = "".join(
        char for char in text.lower() if char in " -_" or unicodedata.category(char)[0] in "LNM"
    ).replace(" ", "-")
    anchor = base
    suffix = 0
    while anchor in used:
        suffix += 1
        anchor = f"{base}-{suffix}"
    return anchor


def _plain_text(tokens: list[Token]) -> str:
    parts: list[str] = []
    for token in tokens:
        match token.type:
            case "image":
                parts.append(_plain_text(token.children or []))
            case "softbreak" | "hardbreak":
                parts.append(" ")
            case "text" | "code_inline":
                parts.append(token.content)
    return "".join(parts)


def parse_document(path: Path, text: str) -> Document:
    tokens = MarkdownIt("commonmark").enable(["table", "strikethrough"]).parse(text)
    html = _Anchors()
    anchors: set[str] = set()
    links: list[Link] = []
    blocks: list[CodeBlock] = []
    diagnostics: list[Diagnostic] = []
    sections: list[tuple[int, str]] = []
    previous_level = 0

    for index, token in enumerate(tokens):
        line = token.map[0] + 1 if token.map else 1
        if token.type == "heading_open":
            level = int(token.tag[1:])
            heading = _plain_text(tokens[index + 1].children or [])
            anchors.add(_heading_anchor(heading, anchors))
            if level > previous_level + 1:
                diagnostics.append(
                    Diagnostic(path, line, 1, "MD001", f"heading skips to level {level}")
                )
            previous_level = level
            while sections and sections[-1][0] >= level:
                sections.pop()
            sections.append((level, heading))

        if token.type == "fence" and token.map:
            start, end = token.map
            # A closed fence spans its opening, content and closing lines.
            # Count the parser's normalized content, including in lists/quotes,
            # so an over-indented fence-like content line cannot fake closure.
            if end - start != token.content.count("\n") + 2:
                diagnostics.append(Diagnostic(path, line, 1, "MD002", "unclosed code fence"))
            language = token.info.split()[0] if token.info.strip() else ""
            if not language:
                diagnostics.append(
                    Diagnostic(path, line, 1, "MD003", "code fence needs a language tag")
                )
            blocks.append(
                CodeBlock(path, line + 1, language, token.content, tuple(s[1] for s in sections))
            )

        for child in [token, *(token.children or [])]:
            if child.type in {"html_inline", "html_block"}:
                html.feed(child.content)
            target = None
            if child.type == "link_open":
                target = child.attrGet("href")
            elif child.type == "image":
                target = child.attrGet("src")
            if isinstance(target, str):
                links.append(Link(target, line))

    anchors.update(html.values)
    return Document(path, frozenset(anchors), tuple(links), tuple(blocks), tuple(diagnostics))


def read_document(path: Path) -> Document:
    return parse_document(path, path.read_text(encoding="utf-8"))


def check_links(documents: dict[Path, Document], root: Path) -> list[Diagnostic]:
    diagnostics: list[Diagnostic] = []
    # Referenced Markdown outside the selected set is read to resolve anchors,
    # but its own links are not implicitly added to the requested check scope.
    cache = dict(documents)
    for document in documents.values():
        for link in document.links:
            try:
                url = urlsplit(link.target)
            except ValueError:
                diagnostics.append(
                    Diagnostic(document.path, link.line, 1, "MD004", "invalid link URL")
                )
                continue
            if url.scheme or url.netloc:
                continue
            decoded = unquote(url.path)
            if decoded.startswith("/"):
                target = root / decoded.lstrip("/")
            elif decoded:
                target = document.path.parent / decoded
            else:
                target = document.path
            message: str | None = None
            try:
                target = target.resolve()
                if not target.exists():
                    message = f"missing local link target: {link.target}"
                elif url.fragment and target.suffix.lower() == ".md":
                    if target not in cache:
                        cache[target] = read_document(target)
                    if unquote(url.fragment) not in cache[target].anchors:
                        message = f"missing heading or HTML anchor: {link.target}"
            except (OSError, ValueError) as error:
                message = f"cannot read link target {link.target}: {error}"
            if message:
                diagnostics.append(Diagnostic(document.path, link.line, 1, "MD004", message))
    return diagnostics
