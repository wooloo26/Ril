#![no_main]

use std::path::PathBuf;

use libfuzzer_sys::fuzz_target;
use ril_source::span::{FileId, SourceFile};
use ril_syntax::{
    cst::CstFile,
    lexer,
    parser::{self, FileKind},
};

fuzz_target!(|data: &[u8]| {
    let path = PathBuf::from("pkg/fuzz.ril");
    let Ok(source) = SourceFile::from_bytes(FileId::from_path(&path), path, data) else {
        return;
    };
    let cst = CstFile::lex(&source);
    if cst.diagnostics.is_empty() {
        assert_eq!(cst.reconstruct(&source), source.text());
    }
    let lexed = lexer::lex_with_recovery(&source);
    let _ = parser::parse_with_recovery(&source, &lexed.tokens, FileKind::Module);
});
