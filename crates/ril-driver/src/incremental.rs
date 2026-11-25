use std::{
    collections::{BTreeMap, HashMap},
    fs,
    path::{Path, PathBuf},
    sync::{Arc, Mutex, PoisonError},
};

use ril_backend::mir;
use ril_base::{
    diag::{Code, Diagnostic},
    span::{FileId, SourceFile, SourceMap, Span},
};
use ril_frontend::{
    hir, lexer,
    parser::{self, FileKind},
};
use ril_sema::{access::Analysis, iface::Interface, ty::TypedProgram};
use ril_test::{CheckResult, Stage, Unit};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

use crate::CompileOptions;

const DISK_SCHEMA_VERSION: u32 = 2;

pub(crate) type ContentDigest = [u8; 32];

pub(crate) fn sha256(bytes: &[u8]) -> ContentDigest {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher.finalize().into()
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct QueryStats {
    pub interface_decode_hits: usize,
    pub interface_decode_misses: usize,
    pub parse_hits: usize,
    pub parse_misses: usize,
    pub check_hits: usize,
    pub check_misses: usize,
    pub type_hits: usize,
    pub type_misses: usize,
    pub access_hits: usize,
    pub access_misses: usize,
    pub interface_build_hits: usize,
    pub interface_build_misses: usize,
    pub mir_hits: usize,
    pub mir_misses: usize,
    pub clif_hits: usize,
    pub clif_misses: usize,
    pub object_hits: usize,
    pub object_misses: usize,
    pub disk_hits: usize,
    pub disk_misses: usize,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize)]
pub(crate) enum FileFingerprint {
    Source { path: PathBuf, hash: ContentDigest },
    Interface { path: PathBuf, abi_hash: String },
    InvalidInterface { path: PathBuf, hash: ContentDigest },
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize)]
pub(crate) struct PackageKey {
    pub(crate) unit: String,
    pub(crate) entry: PathBuf,
    pub(crate) files: Vec<FileFingerprint>,
}

impl PackageKey {
    pub(crate) fn new(unit: Unit, entry: PathBuf, files: Vec<FileFingerprint>) -> Self {
        let unit = match unit {
            Unit::Bin => "bin",
            Unit::Lib => "lib",
            Unit::Decl => "decl",
            Unit::Snippet => "snippet",
        };
        Self {
            unit: unit.into(),
            entry,
            files,
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize)]
pub(crate) struct ParseKey {
    pub(crate) file_id: usize,
    pub(crate) path: PathBuf,
    pub(crate) kind: u8,
    pub(crate) hash: ContentDigest,
}

impl ParseKey {
    pub(crate) fn new(file_id: FileId, path: PathBuf, kind: FileKind, hash: ContentDigest) -> Self {
        let kind = match kind {
            FileKind::Module => 0,
            FileKind::Interface => 1,
            FileKind::Executable => 2,
            FileKind::Foreign => 3,
            FileKind::Snippet => 4,
        };
        Self {
            file_id: file_id.0,
            path,
            kind,
            hash,
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize)]
pub(crate) struct TypeKey {
    pub(crate) package: PackageKey,
    pub(crate) budget: Option<u64>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize)]
pub(crate) struct MirKey {
    pub(crate) access: TypeKey,
    pub(crate) codegen_hashes: Vec<(PathBuf, String)>,
    pub(crate) options: CompileOptions,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize)]
pub(crate) struct CheckKey {
    pub(crate) package: PackageKey,
    pub(crate) budget: Option<u64>,
    pub(crate) stage: u8,
    pub(crate) options: Option<CompileOptions>,
}

impl CheckKey {
    pub(crate) fn new(
        package: PackageKey,
        budget: Option<u64>,
        stage: Stage,
        options: CompileOptions,
    ) -> Self {
        let stage_code = match stage {
            Stage::Source => 0,
            Stage::Lex => 1,
            Stage::Parse => 2,
            Stage::Hir => 3,
            Stage::Type => 4,
            Stage::Access => 5,
            Stage::Mir => 6,
            Stage::Run => 7,
        };
        Self {
            package,
            budget,
            stage: stage_code,
            options: (stage >= Stage::Mir).then_some(options),
        }
    }
}

type AnalysisPair = (Arc<TypedProgram>, Arc<Analysis>);
type AnalysisResult = Result<AnalysisPair, Vec<Diagnostic>>;

#[derive(Default)]
struct CacheState {
    stats: QueryStats,
    decoded_interfaces: HashMap<ContentDigest, Result<Arc<Interface>, String>>,
    parsed_files: HashMap<ParseKey, Result<hir::File, Vec<Diagnostic>>>,
    checks: HashMap<CheckKey, (SourceMap, CheckResult)>,
    typed: HashMap<TypeKey, Result<Arc<TypedProgram>, Vec<Diagnostic>>>,
    analysis: HashMap<TypeKey, AnalysisResult>,
    interfaces: HashMap<TypeKey, Result<Arc<Interface>, Vec<Diagnostic>>>,
    mir: HashMap<MirKey, Result<Arc<mir::Program>, Vec<Diagnostic>>>,
    clif: HashMap<MirKey, Result<Arc<String>, Vec<Diagnostic>>>,
    objects: HashMap<MirKey, Result<Arc<Vec<u8>>, Vec<Diagnostic>>>,
}

pub struct IncrementalCache {
    disk_dir: Option<PathBuf>,
    state: Mutex<CacheState>,
}

impl std::fmt::Debug for IncrementalCache {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("IncrementalCache")
            .field("disk_dir", &self.disk_dir)
            .field("stats", &self.stats())
            .finish()
    }
}

impl Default for IncrementalCache {
    fn default() -> Self {
        Self::new()
    }
}

impl IncrementalCache {
    pub fn new() -> Self {
        Self {
            disk_dir: None,
            state: Mutex::new(CacheState::default()),
        }
    }

    pub fn with_disk_dir(dir: PathBuf) -> Self {
        Self {
            disk_dir: Some(dir),
            state: Mutex::new(CacheState::default()),
        }
    }

    pub fn stats(&self) -> QueryStats {
        self.lock().stats
    }

    pub fn reset_stats(&self) {
        self.lock().stats = QueryStats::default();
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, CacheState> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    pub(crate) fn decode_interface(&self, bytes: &[u8]) -> Result<Arc<Interface>, String> {
        let digest = sha256(bytes);
        {
            let mut state = self.lock();
            if let Some(hit) = state.decoded_interfaces.get(&digest).cloned() {
                state.stats.interface_decode_hits += 1;
                return hit;
            }
            state.stats.interface_decode_misses += 1;
        }
        let decoded = Interface::decode(bytes).map(Arc::new);
        self.lock()
            .decoded_interfaces
            .insert(digest, decoded.clone());
        decoded
    }

    pub(crate) fn parse_file(
        &self,
        source: &SourceFile,
        kind: FileKind,
        content_hash: ContentDigest,
    ) -> Result<hir::File, Vec<Diagnostic>> {
        let key = ParseKey::new(source.id(), source.path().to_path_buf(), kind, content_hash);
        {
            let mut state = self.lock();
            if let Some(hit) = state.parsed_files.get(&key).cloned() {
                state.stats.parse_hits += 1;
                return hit;
            }
            state.stats.parse_misses += 1;
        }
        let lexed = lexer::lex_with_recovery(source);
        let parsed = if !lexed.diagnostics.is_empty() {
            Err(lexed.diagnostics)
        } else {
            let out = parser::parse_with_recovery(source, &lexed.tokens, kind);
            if !out.diagnostics.is_empty() {
                Err(out.diagnostics)
            } else {
                Ok(hir::File::new(source.clone(), kind, out.ast, lexed.tokens))
            }
        };
        self.lock().parsed_files.insert(key, parsed.clone());
        parsed
    }

    pub(crate) fn get_check(&self, key: &CheckKey) -> Option<(SourceMap, CheckResult)> {
        let mut state = self.lock();
        if let Some(hit) = state.checks.get(key).cloned() {
            state.stats.check_hits += 1;
            return Some(hit);
        }
        state.stats.check_misses += 1;
        None
    }

    pub(crate) fn put_check(&self, key: CheckKey, sources: SourceMap, result: CheckResult) {
        self.lock().checks.insert(key, (sources, result));
    }

    pub(crate) fn read_disk_check(&self, key: &CheckKey) -> Option<CheckResult> {
        let path = self.disk_path("check", "json", key)?;
        let Ok(bytes) = fs::read(&path) else {
            self.lock().stats.disk_misses += 1;
            return None;
        };
        let Ok(entry) = serde_json::from_slice::<DiskCheckEntry>(&bytes) else {
            self.lock().stats.disk_misses += 1;
            return None;
        };
        let Some(result) = entry.into_check_result() else {
            self.lock().stats.disk_misses += 1;
            return None;
        };
        self.lock().stats.disk_hits += 1;
        Some(result)
    }

    pub(crate) fn write_disk_check(&self, key: &CheckKey, result: &CheckResult) {
        let Some(path) = self.disk_path("check", "json", key) else {
            return;
        };
        let entry = DiskCheckEntry::from(result);
        if let Ok(bytes) = serde_json::to_vec(&entry) {
            write_atomic(&path, &bytes);
        }
    }

    pub(crate) fn get_typed(
        &self,
        key: &TypeKey,
    ) -> Option<Result<Arc<TypedProgram>, Vec<Diagnostic>>> {
        let mut state = self.lock();
        if let Some(hit) = state.typed.get(key).cloned() {
            state.stats.type_hits += 1;
            return Some(hit);
        }
        state.stats.type_misses += 1;
        None
    }

    pub(crate) fn put_typed(
        &self,
        key: TypeKey,
        value: Result<Arc<TypedProgram>, Vec<Diagnostic>>,
    ) {
        self.lock().typed.insert(key, value);
    }

    pub(crate) fn get_analysis(&self, key: &TypeKey) -> Option<AnalysisResult> {
        let mut state = self.lock();
        if let Some(hit) = state.analysis.get(key).cloned() {
            state.stats.access_hits += 1;
            return Some(hit);
        }
        state.stats.access_misses += 1;
        None
    }

    pub(crate) fn put_analysis(&self, key: TypeKey, value: AnalysisResult) {
        self.lock().analysis.insert(key, value);
    }

    pub(crate) fn get_interface(
        &self,
        key: &TypeKey,
    ) -> Option<Result<Arc<Interface>, Vec<Diagnostic>>> {
        {
            let mut state = self.lock();
            if let Some(hit) = state.interfaces.get(key).cloned() {
                state.stats.interface_build_hits += 1;
                return Some(hit);
            }
            state.stats.interface_build_misses += 1;
        }
        let path = self.disk_path("iface", "rili", key)?;
        let Ok(bytes) = fs::read(&path) else {
            self.lock().stats.disk_misses += 1;
            return None;
        };
        let Ok(interface) = Interface::decode(&bytes) else {
            self.lock().stats.disk_misses += 1;
            return None;
        };
        let interface = Arc::new(interface);
        let mut state = self.lock();
        state.stats.disk_hits += 1;
        state
            .interfaces
            .insert(key.clone(), Ok(Arc::clone(&interface)));
        Some(Ok(interface))
    }

    pub(crate) fn put_interface(
        &self,
        key: TypeKey,
        value: Result<Arc<Interface>, Vec<Diagnostic>>,
    ) {
        if let Ok(interface) = &value
            && let Some(path) = self.disk_path("iface", "rili", &key)
            && let Ok(bytes) = interface.encode()
        {
            write_atomic(&path, &bytes);
        }
        self.lock().interfaces.insert(key, value);
    }

    pub(crate) fn get_mir(
        &self,
        key: &MirKey,
    ) -> Option<Result<Arc<mir::Program>, Vec<Diagnostic>>> {
        let mut state = self.lock();
        if let Some(hit) = state.mir.get(key).cloned() {
            state.stats.mir_hits += 1;
            return Some(hit);
        }
        state.stats.mir_misses += 1;
        None
    }

    pub(crate) fn put_mir(&self, key: MirKey, value: Result<Arc<mir::Program>, Vec<Diagnostic>>) {
        self.lock().mir.insert(key, value);
    }

    pub(crate) fn get_clif(&self, key: &MirKey) -> Option<Result<Arc<String>, Vec<Diagnostic>>> {
        let mut state = self.lock();
        if let Some(hit) = state.clif.get(key).cloned() {
            state.stats.clif_hits += 1;
            return Some(hit);
        }
        state.stats.clif_misses += 1;
        None
    }

    pub(crate) fn put_clif(&self, key: MirKey, value: Result<Arc<String>, Vec<Diagnostic>>) {
        self.lock().clif.insert(key, value);
    }

    pub(crate) fn get_object(&self, key: &MirKey) -> Option<Result<Arc<Vec<u8>>, Vec<Diagnostic>>> {
        {
            let mut state = self.lock();
            if let Some(hit) = state.objects.get(key).cloned() {
                state.stats.object_hits += 1;
                return Some(hit);
            }
            state.stats.object_misses += 1;
        }
        let path = self.disk_path("obj", "o", key)?;
        let Ok(bytes) = fs::read(&path) else {
            self.lock().stats.disk_misses += 1;
            return None;
        };
        let object = Arc::new(bytes);
        let mut state = self.lock();
        state.stats.disk_hits += 1;
        state.objects.insert(key.clone(), Ok(Arc::clone(&object)));
        Some(Ok(object))
    }

    pub(crate) fn put_object(&self, key: MirKey, value: Result<Arc<Vec<u8>>, Vec<Diagnostic>>) {
        if let Ok(bytes) = &value
            && let Some(path) = self.disk_path("obj", "o", &key)
        {
            write_atomic(&path, bytes);
        }
        self.lock().objects.insert(key, value);
    }

    fn disk_path<K: Serialize>(&self, prefix: &str, ext: &str, key: &K) -> Option<PathBuf> {
        let dir = self.disk_dir.as_ref()?;
        let payload = serde_json::to_vec(&(
            DISK_SCHEMA_VERSION,
            env!("CARGO_PKG_VERSION"),
            std::env::consts::ARCH,
            std::env::consts::OS,
            prefix,
            key,
        ))
        .ok()?;
        let hash = hex_digest(&sha256(&payload));
        Some(
            dir.join(format!("v{DISK_SCHEMA_VERSION}"))
                .join(format!("{prefix}-{hash}.{ext}")),
        )
    }
}

fn hex_digest(bytes: &ContentDigest) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        let _ = write!(out, "{byte:02x}");
    }
    out
}

fn write_atomic(path: &Path, bytes: &[u8]) {
    use std::sync::atomic::{AtomicU64, Ordering};
    static TMP_SEQ: AtomicU64 = AtomicU64::new(0);

    let Some(parent) = path.parent() else {
        return;
    };
    if fs::create_dir_all(parent).is_err() {
        return;
    }
    let seq = TMP_SEQ.fetch_add(1, Ordering::Relaxed);
    let tmp = path.with_extension(format!("tmp.{}.{seq}", std::process::id()));
    if fs::write(&tmp, bytes).is_ok() {
        let _ = fs::rename(&tmp, path);
    }
}

#[derive(Serialize, Deserialize)]
struct DiskLabel {
    span: (usize, usize, usize),
    message: String,
}

#[derive(Serialize, Deserialize)]
struct DiskDiagnostic {
    severity: String,
    code: Option<String>,
    primary: Option<(usize, usize, usize)>,
    message: String,
    labels: Vec<DiskLabel>,
    notes: Vec<String>,
    help: Vec<String>,
}

#[derive(Serialize, Deserialize)]
struct DiskCheckEntry {
    diagnostics: Vec<DiskDiagnostic>,
    signatures: BTreeMap<String, String>,
    file_paths: BTreeMap<usize, PathBuf>,
}

impl From<&CheckResult> for DiskCheckEntry {
    fn from(result: &CheckResult) -> Self {
        Self {
            diagnostics: result
                .diagnostics
                .iter()
                .map(|diag| DiskDiagnostic {
                    severity: diag.severity.as_str().to_owned(),
                    code: diag.code.map(|code| code.as_str().to_owned()),
                    primary: diag.primary.map(|span| (span.file.0, span.start, span.end)),
                    message: diag.message.clone(),
                    labels: diag
                        .labels()
                        .iter()
                        .map(|label| DiskLabel {
                            span: (label.span.file.0, label.span.start, label.span.end),
                            message: label.message.clone(),
                        })
                        .collect(),
                    notes: diag.notes().to_vec(),
                    help: diag.help().to_vec(),
                })
                .collect(),
            signatures: result.signatures.clone(),
            file_paths: result
                .file_paths
                .iter()
                .map(|(id, path)| (id.0, path.clone()))
                .collect(),
        }
    }
}

impl DiskCheckEntry {
    fn into_check_result(self) -> Option<CheckResult> {
        let mut diagnostics = Vec::with_capacity(self.diagnostics.len());
        for item in self.diagnostics {
            let severity = match item.severity.as_str() {
                "warning" => ril_base::diag::Severity::Warning,
                _ => ril_base::diag::Severity::Error,
            };
            let code = match item.code {
                Some(text) => Some(text.parse::<Code>().ok()?),
                None => None,
            };
            let primary = item
                .primary
                .map(|(file, start, end)| Span::new(FileId(file), start, end));
            let mut diag = Diagnostic::unsupported(item.message);
            diag.severity = severity;
            diag.code = code;
            diag.primary = primary;
            for label in item.labels {
                diag = diag.with_label(
                    Span::new(FileId(label.span.0), label.span.1, label.span.2),
                    label.message,
                );
            }
            for note in item.notes {
                diag = diag.with_note(note);
            }
            for help in item.help {
                diag = diag.with_help(help);
            }
            diagnostics.push(diag);
        }
        let file_paths = self
            .file_paths
            .into_iter()
            .map(|(id, path)| (FileId(id), path))
            .collect();
        Some(CheckResult {
            diagnostics,
            signatures: self.signatures,
            file_paths,
        })
    }
}
