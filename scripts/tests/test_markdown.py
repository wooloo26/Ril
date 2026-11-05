from pathlib import Path

import pytest

from ril_doccheck.markdown import check_links, parse_document


def test_headings_use_visible_text_and_unique_unicode_anchors(tmp_path: Path) -> None:
    document = parse_document(
        tmp_path / "test.md",
        "# Hello *世界* `Ril` & modes!\n## Same\n## Same\n## Same-1\n## Same\n",
    )
    assert document.anchors == {"hello-世界-ril--modes", "same", "same-1", "same-1-1", "same-2"}
    assert not document.diagnostics


def test_fence_contents_do_not_create_headings_or_links(tmp_path: Path) -> None:
    document = parse_document(
        tmp_path / "test.md", "# Title\n\n```text\n# Fake\n[bad](missing.md)\n```\n"
    )
    assert document.anchors == {"title"}
    assert not document.links
    assert not document.diagnostics


@pytest.mark.parametrize(
    ("text", "code", "line"),
    [
        ("# Title\n### Jump\n", "MD001", 2),
        ("# Title\n```text\nunfinished\n", "MD002", 2),
        ("# Title\n```\ncontent\n```\n", "MD003", 2),
        ("# Title\n~~~text\ncontent\n```\n", "MD002", 2),
        ("# Title\n```text\n", "MD002", 2),
        ("# Title\n```text\n    ```\n", "MD002", 2),
        ("# Title\n> ```text\n> unfinished\n\nOutside\n", "MD002", 2),
    ],
)
def test_structural_diagnostics(tmp_path: Path, text: str, code: str, line: int) -> None:
    document = parse_document(tmp_path / "test.md", text)
    assert [(d.code, d.line) for d in document.diagnostics] == [(code, line)]


@pytest.mark.parametrize(
    "text",
    [
        "# Title\n\n~~~~text\ncontent\n~~~~~\n",
        "# Title\n\n> ```text\n> content\n> ```\n",
        "# Title\n\n- item\n\n  ```text\n  content\n  ```\n",
        "# Title\n\n```text\n```",
    ],
)
def test_valid_fences(tmp_path: Path, text: str) -> None:
    assert not parse_document(tmp_path / "test.md", text).diagnostics


def test_local_links_images_and_anchors(tmp_path: Path) -> None:
    target = tmp_path / "other file.md"
    target.write_text('# Other\n\n## 中文 `Code`\n\n<a id="explicit"></a>\n', encoding="utf-8")
    (tmp_path / "image.png").write_bytes(b"image")
    source = tmp_path / "source.md"
    source.write_text(
        "# Source\n"
        "[ok](other%20file.md#%E4%B8%AD%E6%96%87-code)\n\n"
        "[html](other%20file.md#explicit)\n\n"
        "[self](#source)\n\n"
        "[root](/other%20file.md#other)\n\n"
        "![image](image.png)\n\n"
        "[remote](https://example.invalid/path#missing)\n\n"
        "[email](mailto:test@example.invalid)\n",
        encoding="utf-8",
    )
    document = parse_document(source, source.read_text(encoding="utf-8"))
    assert not check_links({source: document}, tmp_path)


def test_broken_links_and_images_have_locations(tmp_path: Path) -> None:
    path = tmp_path / "test.md"
    document = parse_document(
        path, "# Title\n\n[bad](#missing)\n\n[missing](absent.md)\n\n![missing](absent.png)\n"
    )
    diagnostics = check_links({path: document}, tmp_path)
    assert [(d.code, d.line) for d in diagnostics] == [("MD004", 3), ("MD004", 5), ("MD004", 7)]


def test_reference_links_are_checked(tmp_path: Path) -> None:
    path = tmp_path / "test.md"
    document = parse_document(path, "# Title\n\n[bad][ref]\n\n[ref]: missing.md\n")
    assert len(check_links({path: document}, tmp_path)) == 1


def test_invalid_filesystem_link_is_a_diagnostic(tmp_path: Path) -> None:
    path = tmp_path / "test.md"
    document = parse_document(path, "# Title\n\n[invalid](bad%00path.md)\n")
    diagnostics = check_links({path: document}, tmp_path)
    assert [(d.code, d.line) for d in diagnostics] == [("MD004", 3)]


def test_code_block_retains_section_context_and_line(tmp_path: Path) -> None:
    document = parse_document(
        tmp_path / "test.md", '# Title\n\n## Grammar Notation\n\n```ebnf\nRule ::= "x"\n```\n'
    )
    assert document.blocks[0].sections == ("Title", "Grammar Notation")
    assert document.blocks[0].line == 6
