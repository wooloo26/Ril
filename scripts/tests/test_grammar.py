from pathlib import Path

import pytest

from doc_check.grammar import check_grammar
from doc_check.markdown import CodeBlock


def block(content: str, *, section: str = "Grammar", line: int = 10) -> CodeBlock:
    return CodeBlock(Path("test.md"), line, "ebnf", content, (section,))


def test_spec_notation_and_lexical_classes() -> None:
    content = r"""Name ::= [A-Z] { [a-zA-Z0-9] }
Snake ::= [a-z] [a-z0-9]* { "_" [a-z0-9]+ }
Start ::= Name [ Snake ] { ( Name | "str" | 'quoted' ) } "\"
"""
    assert not check_grammar([block(content)])


def test_compact_optional_names_remain_references() -> None:
    diagnostics = check_grammar([block("Start ::= [Missing]\n")])
    assert [d.code for d in diagnostics] == ["EBNF003"]
    assert "Missing" in diagnostics[0].message


def test_references_resolve_across_blocks_in_both_directions() -> None:
    blocks = [block("First ::= Second\n"), block('Second ::= First | "x"\n', line=30)]
    assert not check_grammar(blocks)


def test_literals_are_not_nonterminal_references() -> None:
    assert not check_grammar([block("Start ::= \"NotDefined\" | 'AlsoNotDefined'\n")])


def test_multiline_productions_preserve_reference_locations() -> None:
    diagnostics = check_grammar([block('Start ::= "x"\n        | Missing\n')])
    assert [(d.code, d.line, d.column) for d in diagnostics] == [("EBNF003", 11, 11)]


@pytest.mark.parametrize(
    "content",
    [
        "Start := Other\n",
        "Start ::=\n",
        'Start ::= [ "x" }\n',
        'Start ::= ( "x"\n',
        'Start ::= "unterminated\n',
        'Start ::= "x" |\n',
        "Start ::= [Z-A]\n",
        "Start ::= [A-Z\n",
        "",
        'Start ::= "x" ???\n',
    ],
)
def test_invalid_grammar_is_rejected(content: str) -> None:
    assert "EBNF001" in {d.code for d in check_grammar([block(content)])}


def test_duplicate_productions_are_rejected() -> None:
    diagnostics = check_grammar([block('Same ::= "x"\n'), block('Same ::= "y"\n', line=30)])
    assert [(d.code, d.line) for d in diagnostics] == [("EBNF002", 30)]


def test_explicit_external_does_not_hide_other_missing_references() -> None:
    diagnostics = check_grammar(
        [block("Start ::= SourceChar Missing\n")], externals=frozenset({"SourceChar"})
    )
    assert len(diagnostics) == 1
    assert "Missing" in diagnostics[0].message


def test_notation_is_parsed_without_exporting_metavariables() -> None:
    diagnostics = check_grammar(
        [block("Choice ::= A | B\n", section="Grammar Notation"), block("Start ::= Choice\n")],
        notation_sections=frozenset({"Grammar Notation"}),
    )
    assert len(diagnostics) == 1
    assert diagnostics[0].code == "EBNF003"
    assert "Choice" in diagnostics[0].message


def test_notation_still_has_syntax_checks() -> None:
    diagnostics = check_grammar(
        [block('Choice ::= [ "x"\n', section="Grammar Notation")],
        notation_sections=frozenset({"Grammar Notation"}),
    )
    assert [d.code for d in diagnostics] == ["EBNF001"]
