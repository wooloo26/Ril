//! Salsa inputs and deterministic queries. Filesystem I/O belongs to the driver.
use salsa::Setter;

#[salsa::input]
pub struct SourceInput {
    #[returns(ref)]
    pub bytes: Vec<u8>,
}

#[salsa::db]
#[derive(Clone, Default)]
pub struct Database {
    storage: salsa::Storage<Self>,
}
#[salsa::db]
impl salsa::Database for Database {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceFacts {
    pub length: usize,
    pub invalid_utf8_at: Option<usize>,
}

#[salsa::tracked]
pub fn source_facts(db: &dyn salsa::Database, source: SourceInput) -> SourceFacts {
    let bytes = source.bytes(db);
    SourceFacts {
        length: bytes.len(),
        invalid_utf8_at: std::str::from_utf8(bytes).err().map(|e| e.valid_up_to()),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedSource {
    pub program: ril_syntax::ast::Program,
    pub diagnostics: Vec<ril_compiler_core::diagnostic::Diagnostic>,
    pub incomplete: bool,
}

#[salsa::tracked]
pub fn parsed_source(db: &dyn salsa::Database, source: SourceInput, file: u32) -> ParsedSource {
    let bytes = source.bytes(db);
    let Ok(text) = std::str::from_utf8(bytes) else {
        return ParsedSource {
            program: Default::default(),
            diagnostics: vec![],
            incomplete: true,
        };
    };
    let parsed = ril_syntax::parse_file(text, ril_compiler_core::source::FileId(file));
    ParsedSource {
        program: parsed.program,
        diagnostics: parsed.diagnostics,
        incomplete: parsed.incomplete,
    }
}

pub(crate) fn update_source(db: &mut Database, source: SourceInput, bytes: Vec<u8>) {
    source.set_bytes(db).to(bytes);
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    };
    #[test]
    fn query_reuses_results_and_invalidates_changed_input() {
        let executions = Arc::new(AtomicUsize::new(0));
        let count = executions.clone();
        let mut db = Database {
            storage: salsa::Storage::new(Some(Box::new(move |event| {
                if matches!(event.kind, salsa::EventKind::WillExecute { .. }) {
                    count.fetch_add(1, Ordering::SeqCst);
                }
            }))),
        };
        let source = SourceInput::new(&db, b"abc".to_vec());
        assert_eq!(source_facts(&db, source).length, 3);
        let first = executions.load(Ordering::SeqCst);
        assert!(first > 0);
        assert_eq!(source_facts(&db, source).length, 3);
        assert_eq!(executions.load(Ordering::SeqCst), first);
        source.set_bytes(&mut db).to(vec![0xff]);
        assert_eq!(source_facts(&db, source).invalid_utf8_at, Some(0));
        assert!(executions.load(Ordering::SeqCst) > first);
    }
}
