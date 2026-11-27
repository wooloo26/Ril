use std::path::{Path, PathBuf};

use ril_source::span::{FileId, SourceFile};
use ril_syntax::{
    directive::is_suite_file,
    fmt,
    lexer::{self, TriviaKind},
    parser,
};

fn collect_ril(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_ril(&path, out);
        } else if path.extension().is_some_and(|e| e == "ril") {
            out.push(path);
        }
    }
}

fn comment_texts(source: &SourceFile, lexed: &lexer::LexOutput) -> Vec<String> {
    lexed
        .trivia
        .iter()
        .filter(|t| t.kind == TriviaKind::LineComment)
        .map(|t| {
            source
                .text()
                .get(t.span.start..t.span.end)
                .unwrap_or_default()
                .trim_end_matches([' ', '\t', '\r'])
                .to_owned()
        })
        .collect()
}

#[test]
fn corpus_std_and_examples_preserve_syntax_comments_and_idempotency() {
    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repo root");
    let mut files = Vec::new();
    collect_ril(&repo_root.join("std"), &mut files);
    collect_ril(&repo_root.join("examples"), &mut files);
    files.sort();
    assert!(!files.is_empty(), "expected std/ and examples/ .ril files");

    for path in files {
        let bytes = std::fs::read(&path).expect("read .ril");
        let text = String::from_utf8(bytes.clone()).expect("utf-8");
        if is_suite_file(&text) {
            continue;
        }
        let source = SourceFile::from_bytes(FileId::from_path(&path), path.clone(), &bytes)
            .expect("source file");
        let lex0 = lexer::lex_with_recovery(&source);
        assert!(
            lex0.diagnostics.is_empty(),
            "lex failed for {}",
            path.display()
        );
        let kind = parser::infer_file_kind(&source, &lex0.tokens);
        let comments0 = comment_texts(&source, &lex0);

        let out1 = fmt::format_source_with_lex(&source, kind, lex0)
            .unwrap_or_else(|e| panic!("fmt failed for {}: {e:?}", path.display()));

        // Well-formedness invariants: LF only, no trailing spaces, single trailing newline.
        assert!(!out1.contains('\r'), "CRLF in {}", path.display());
        if !out1.is_empty() {
            assert!(
                out1.ends_with('\n'),
                "missing trailing newline in {}",
                path.display()
            );
            assert!(
                !out1.ends_with("\n\n"),
                "extra trailing newline in {}",
                path.display()
            );
        }
        for (i, line) in out1.lines().enumerate() {
            assert!(
                !line.ends_with([' ', '\t']),
                "trailing whitespace in {}:{}",
                path.display(),
                i + 1
            );
        }

        // Round-trip lex + parse + comment preservation + strict idempotency.
        let src1 = SourceFile::from_bytes(FileId::from_path(&path), path.clone(), out1.as_bytes())
            .expect("formatted utf-8");
        let lex1 = lexer::lex_with_recovery(&src1);
        assert!(
            lex1.diagnostics.is_empty(),
            "re-lex failed for {}: {:?}",
            path.display(),
            lex1.diagnostics
        );
        let comments1 = comment_texts(&src1, &lex1);
        assert_eq!(
            comments0,
            comments1,
            "comments altered in {}",
            path.display()
        );
        let parsed1 = parser::parse_with_recovery(&src1, &lex1.tokens, kind);
        assert!(
            parsed1.diagnostics.is_empty(),
            "re-parse failed for {}: {:?}",
            path.display(),
            parsed1.diagnostics
        );
        let out2 = fmt::format_source_with_lex(&src1, kind, lex1)
            .unwrap_or_else(|e| panic!("second fmt failed for {}: {e:?}", path.display()));
        assert_eq!(out1, out2, "non-idempotent fmt for {}", path.display());
    }
}
