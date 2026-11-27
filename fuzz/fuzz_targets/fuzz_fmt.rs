#![no_main]

use std::path::PathBuf;

use libfuzzer_sys::fuzz_target;
use ril_source::span::{FileId, SourceFile};
use ril_syntax::{fmt, lexer, parser};

fuzz_target!(|data: &[u8]| {
    let Ok(source) = SourceFile::from_bytes(FileId(1), PathBuf::from("pkg/fuzz.ril"), data) else {
        return;
    };
    for kind in [
        parser::FileKind::Module,
        parser::FileKind::Executable,
        parser::FileKind::Snippet,
    ] {
        let lexed = lexer::lex_with_recovery(&source);
        let parsed = parser::parse_with_recovery(&source, &lexed.tokens, kind);
        if lexed.diagnostics.is_empty() && parsed.diagnostics.is_empty() {
            let out1 = fmt::format_source(&source, kind).expect("valid AST must format");
            let src1 =
                SourceFile::from_bytes(FileId(1), PathBuf::from("pkg/fuzz.ril"), out1.as_bytes())
                    .expect("formatted output must be valid utf-8");
            let lex1 = lexer::lex_with_recovery(&src1);
            assert!(
                lex1.diagnostics.is_empty(),
                "formatted output failed lexing: {:?}",
                lex1.diagnostics
            );
            let parsed1 = parser::parse_with_recovery(&src1, &lex1.tokens, kind);
            assert!(
                parsed1.diagnostics.is_empty(),
                "formatted output failed parsing: {:?}",
                parsed1.diagnostics
            );
            let out2 = fmt::format_source(&src1, kind).expect("formatted output must reformat");
            assert_eq!(out1, out2, "formatter must be strictly idempotent");
        } else {
            assert!(fmt::format_source(&source, kind).is_err());
        }
    }
});
