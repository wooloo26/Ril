from pathlib import Path

import pytest

from doc_check.cli import main, markdown_files


def test_cli_success(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    (tmp_path / "test.md").write_text('# Title\n\n```ebnf\nStart ::= "x"\n```\n', encoding="utf-8")
    assert main(["--root", str(tmp_path)]) == 0
    assert "1 Markdown files and 1 EBNF blocks; 0 errors" in capsys.readouterr().out


def test_cli_validation_failure(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    (tmp_path / "test.md").write_text("# Title\n\n[bad](missing.md)\n", encoding="utf-8")
    assert main(["--root", str(tmp_path)]) == 1
    assert "test.md:3:1: MD004" in capsys.readouterr().out


def test_cli_bad_input(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    assert main([str(tmp_path / "absent.md")]) == 2
    assert "input does not exist" in capsys.readouterr().err


def test_cli_empty_directory(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    assert main([str(tmp_path)]) == 2
    assert "no Markdown files selected" in capsys.readouterr().err


def test_cli_invalid_utf8_is_a_diagnostic(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    (tmp_path / "test.md").write_bytes(b"\xff")
    assert main(["--root", str(tmp_path)]) == 1
    assert "IO001" in capsys.readouterr().out


def test_discovery_skips_generated_directories_and_deduplicates(tmp_path: Path) -> None:
    wanted = tmp_path / "test.md"
    wanted.write_text("# Title\n", encoding="utf-8")
    for name in (".git", ".venv", ".mypy_cache", "node_modules", "target", "dist"):
        directory = tmp_path / name
        directory.mkdir()
        (directory / "ignored.md").write_text("ignored\n", encoding="utf-8")
    assert markdown_files([tmp_path, wanted]) == [wanted]
