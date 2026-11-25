use std::{
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::Arc,
};

use ril_codegen as cranelift;
use ril_mir as mir;
use ril_source::diag::Diagnostic;
use ril_test::{ExecOutput, Unit, VirtualPackage, run_worker};
use serde::{Deserialize, Serialize};

use crate::{CompileOptions, Compiler, Driver, incremental::MirKey};

type Result<T> = std::result::Result<T, Vec<Diagnostic>>;

fn failure(error: impl ToString) -> Vec<Diagnostic> {
    vec![Diagnostic::unsupported(error.to_string())]
}

impl Compiler {
    pub fn lower(&self, package: &VirtualPackage) -> Result<mir::Program> {
        let (typed, analysis, _, _) = self.analyze_arc(package)?;
        mir::lower_with_options(&typed, &analysis, self.options().lower_options())
            .map_err(|error| vec![error])
    }

    pub fn lower_arc(&self, package: &VirtualPackage) -> Result<Arc<mir::Program>> {
        let (typed, analysis, access, codegen_hashes) = self.analyze_arc(package)?;
        let key = MirKey {
            access,
            codegen_hashes,
            options: self.options(),
        };
        self.lower_with(typed, analysis, key)
    }

    pub fn clif(&self, package: &VirtualPackage) -> Result<String> {
        let (typed, analysis, access, codegen_hashes) = self.analyze_arc(package)?;
        let key = MirKey {
            access,
            codegen_hashes,
            options: self.options(),
        };
        if let Some(cache) = self.cache()
            && let Some(hit) = cache.get_clif(&key)
        {
            return hit.map(|text| (*text).clone());
        }
        let compiled = self.lower_with(typed, analysis, key.clone())?;
        let result =
            cranelift::emit_clif_with_opt(&compiled, self.options().opt_level.to_backend())
                .map(Arc::new)
                .map_err(|err| vec![err]);
        if let Some(cache) = self.cache() {
            cache.put_clif(key, result.clone());
        }
        result.map(|text| (*text).clone())
    }

    pub fn compile_object(&self, package: &VirtualPackage) -> Result<Arc<Vec<u8>>> {
        let prepared = crate::prepare_inputs(package, self.cache());
        let access = crate::incremental::TypeKey {
            package: prepared.package_key.clone(),
            budget: package.budget,
        };
        let key = MirKey {
            access: access.clone(),
            codegen_hashes: prepared.codegen_hashes.clone(),
            options: self.options(),
        };
        if let Some(cache) = self.cache()
            && let Some(hit) = cache.get_object(&key)
        {
            return hit;
        }
        let result = (|| {
            let typed = self.typed_with(package, prepared, access.clone())?;
            let (typed, analysis) = self.analyze_with(typed, access)?;
            let compiled = self.lower_with(typed, analysis, key.clone())?;
            cranelift::object_with_opt(&compiled, self.options().opt_level.to_backend())
                .map(Arc::new)
                .map_err(|err| vec![err])
        })();
        if let Some(cache) = self.cache() {
            cache.put_object(key, result.clone());
        }
        result
    }

    pub fn compile_objects(
        &self,
        package: &VirtualPackage,
        cgu_count: usize,
    ) -> Result<Vec<Vec<u8>>> {
        if cgu_count <= 1 {
            return Ok(vec![(*self.compile_object(package)?).clone()]);
        }
        let compiled = self.lower_arc(package)?;
        cranelift::objects_with_opt(&compiled, cgu_count, self.options().opt_level.to_backend())
            .map_err(|err| vec![err])
    }

    pub fn horn_json(&self, package: &VirtualPackage) -> Result<String> {
        serde_json::to_string_pretty(&self.horn_rules(package)?).map_err(failure)
    }

    pub fn compile_aot(&self, package: &VirtualPackage, output: &Path) -> Result<()> {
        self.compile_aot_with_links(package, output, &[])
    }

    pub fn compile_aot_with_links(
        &self,
        package: &VirtualPackage,
        output: &Path,
        links: &[PathBuf],
    ) -> Result<()> {
        self.compile_aot_with_cgus(package, output, links, 1)
    }

    pub fn compile_aot_with_cgus(
        &self,
        package: &VirtualPackage,
        output: &Path,
        links: &[PathBuf],
        cgu_count: usize,
    ) -> Result<()> {
        let links = links
            .iter()
            .map(|path| {
                path.canonicalize()
                    .map_err(|err| failure(format!("{}: {err}", path.display())))
            })
            .collect::<Result<Vec<_>>>()?;
        if cgu_count <= 1 {
            let object = self.compile_object(package)?;
            link_objects(std::slice::from_ref(&*object), &links, output)
        } else {
            let objects = self.compile_objects(package, cgu_count)?;
            link_objects(&objects, &links, output)
        }
    }

    /// Compile and execute a package directly in the current process via Cranelift JIT
    /// without spawning a worker subprocess. Returns the program's integer exit status.
    pub fn execute_jit_in_process(&self, package: &VirtualPackage) -> Result<i32> {
        let compiled = self.lower_arc(package)?;
        cranelift::jit_with_opt(&compiled, self.options().opt_level.to_backend())
            .map_err(|err| vec![err])
    }

    pub fn execute_jit(&self, package: &VirtualPackage) -> Result<ExecOutput> {
        let executable = std::env::current_exe().map_err(failure)?;
        let temporary = tempfile::NamedTempFile::new().map_err(failure)?;
        let wire = PackageWire::from_package(package, self.options());
        serde_json::to_writer(temporary.as_file(), &wire).map_err(failure)?;
        run_worker(
            Command::new(executable)
                .arg("--__ril_worker")
                .arg(temporary.path()),
        )
        .map_err(failure)
    }
}

impl Driver {
    pub fn lower(&self, package: &VirtualPackage) -> Result<mir::Program> {
        self.with_options(CompileOptions::default()).lower(package)
    }

    pub fn clif(&self, package: &VirtualPackage) -> Result<String> {
        self.with_options(CompileOptions::default()).clif(package)
    }

    pub fn horn_json(&self, package: &VirtualPackage) -> Result<String> {
        self.with_options(CompileOptions::default())
            .horn_json(package)
    }

    pub fn compile_aot(&self, package: &VirtualPackage, output: &Path) -> Result<()> {
        self.compile_aot_with_links(package, output, &[])
    }

    pub fn compile_aot_with_links(
        &self,
        package: &VirtualPackage,
        output: &Path,
        links: &[PathBuf],
    ) -> Result<()> {
        self.with_options(CompileOptions::default())
            .compile_aot_with_links(package, output, links)
    }

    pub fn execute_jit(&self, package: &VirtualPackage) -> Result<ExecOutput> {
        self.with_options(CompileOptions::default())
            .execute_jit(package)
    }

    fn worker(&self, path: &Path) -> Result<i32> {
        let file = fs::File::open(path).map_err(failure)?;
        let wire: PackageWire = serde_json::from_reader(file).map_err(failure)?;
        let options = CompileOptions {
            opt_stack_promote: wire.opt_stack_promote,
            opt_level: wire.opt_level,
        };
        let package = wire.into_package()?;
        let program = self.with_options(options).lower(&package)?;
        cranelift::jit_with_opt(&program, options.opt_level.to_backend()).map_err(|err| vec![err])
    }
}

pub(crate) fn link_objects(objects: &[Vec<u8>], links: &[PathBuf], output: &Path) -> Result<()> {
    let tmp = tempfile::tempdir().map_err(failure)?;
    let mut object_paths = Vec::with_capacity(objects.len());
    for (idx, bytes) in objects.iter().enumerate() {
        let object_path = tmp.path().join(format!("ril_{idx}.o"));
        fs::write(&object_path, bytes).map_err(failure)?;
        object_paths.push(object_path);
    }
    let runtime = runtime_archive()?;
    let mut command = if cfg!(target_env = "msvc") && std::env::var_os("CC").is_none() {
        let mut cmd = Command::new("link.exe");
        cmd.arg("/NOLOGO")
            .arg("/OPT:REF")
            .args(&object_paths)
            .args(links)
            .arg(&runtime)
            .args([
                "ws2_32.lib",
                "userenv.lib",
                "bcrypt.lib",
                "ntdll.lib",
                "advapi32.lib",
            ])
            .arg(format!("/OUT:{}", output.display()));
        cmd
    } else {
        let mut cmd = Command::new(std::env::var_os("CC").unwrap_or_else(|| "cc".into()));
        cmd.args(&object_paths).args(links).arg(&runtime);
        if cfg!(target_os = "linux") {
            cmd.args(["-Wl,--gc-sections", "-ldl", "-lpthread", "-lm"]);
        } else if cfg!(target_os = "macos") {
            cmd.arg("-Wl,-dead_strip");
        }
        cmd.arg("-o").arg(output);
        cmd
    };
    let link = command.output().map_err(failure)?;
    if link.status.success() {
        Ok(())
    } else {
        Err(failure(format!(
            "linker failed ({})\n{}",
            link.status,
            String::from_utf8_lossy(&link.stderr)
        )))
    }
}

pub fn worker_entry() -> Option<i32> {
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref() != Some(OsStr::new("--__ril_worker")) {
        return None;
    }
    let result = args
        .next()
        .ok_or_else(|| failure("missing worker package"))
        .and_then(|path| Driver.worker(Path::new(&path)));
    Some(match result {
        Ok(status) => status,
        Err(diagnostics) => {
            for diagnostic in diagnostics {
                eprintln!("{diagnostic}");
            }
            125
        }
    })
}

fn runtime_archive() -> Result<PathBuf> {
    if let Some(path) = std::env::var_os("RIL_RUNTIME_ARCHIVE") {
        return Ok(path.into());
    }
    let archive_name = if cfg!(target_env = "msvc") {
        "ril_rt.lib"
    } else {
        "libril_rt.a"
    };
    // 1. Check alongside the running `ril` executable (standalone distribution).
    if let Ok(exe) = std::env::current_exe()
        && let Some(dir) = exe.parent()
    {
        let sibling = dir.join(archive_name);
        if sibling.is_file() {
            return Ok(sibling);
        }
    }
    // 2. Content-addressed cached build keyed on runtime sources + rustc version.
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let digest = runtime_source_digest(&root)?;
    let cache_dir = root.join("target/ril-runtime-cache");
    let cached = cache_dir.join(format!("{digest}-{archive_name}"));
    if cached.is_file() {
        return Ok(cached);
    }

    // Serialize first-time build across parallel processes with a lock file + atomic rename.
    fs::create_dir_all(&cache_dir).map_err(failure)?;
    let lock_path = cache_dir.join(format!("{digest}.lock"));
    let _lock = acquire_lock(&lock_path)?;
    if cached.is_file() {
        return Ok(cached);
    }

    let manifest = root.join("runtime/ril-rt-static/Cargo.toml");
    let target = root.join("target/ril-runtime");
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let build = Command::new(cargo)
        .args(["build", "--release", "--locked", "--manifest-path"])
        .arg(manifest)
        .arg("--target-dir")
        .arg(&target)
        .output()
        .map_err(failure)?;
    if !build.status.success() {
        return Err(failure(format!(
            "runtime archive build failed\n{}",
            String::from_utf8_lossy(&build.stderr)
        )));
    }
    let built = target.join("release").join(archive_name);
    let seq = ARCHIVE_TMP_SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let tmp = cache_dir.join(format!("{digest}.tmp.{}.{seq}", std::process::id()));
    fs::copy(&built, &tmp).map_err(failure)?;
    fs::rename(&tmp, &cached).map_err(failure)?;
    Ok(cached)
}

static ARCHIVE_TMP_SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

struct LockGuard(PathBuf);

impl Drop for LockGuard {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn acquire_lock(path: &Path) -> Result<LockGuard> {
    for _ in 0..600 {
        match fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
        {
            Ok(_) => return Ok(LockGuard(path.to_owned())),
            Err(err) if err.kind() == std::io::ErrorKind::AlreadyExists => {
                std::thread::sleep(std::time::Duration::from_millis(50));
            }
            Err(err) => return Err(failure(err)),
        }
    }
    // Stale lock recovery after 30s wait.
    let _ = fs::remove_file(path);
    Ok(LockGuard(path.to_owned()))
}

fn runtime_source_digest(root: &Path) -> Result<String> {
    use sha2::{Digest as _, Sha256};

    let mut hasher = Sha256::new();
    hasher.update(std::env::consts::ARCH.as_bytes());
    hasher.update(b"-");
    hasher.update(std::env::consts::OS.as_bytes());
    if let Ok(out) = Command::new(std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into()))
        .arg("-vV")
        .output()
    {
        hasher.update(&out.stdout);
    }
    let mut files = Vec::new();
    collect_files(&root.join("crates/ril-rt"), &mut files);
    collect_files(&root.join("runtime/ril-rt-static"), &mut files);
    files.sort();
    for path in files {
        if let Ok(bytes) = fs::read(&path) {
            hasher.update(path.to_string_lossy().as_bytes());
            hasher.update(b"\0");
            hasher.update(&bytes);
        }
    }
    let hex = format!("{:x}", hasher.finalize());
    Ok(hex.chars().take(16).collect())
}

fn collect_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            if path.file_name().is_some_and(|n| n == "target") {
                continue;
            }
            collect_files(&path, out);
        } else if path
            .extension()
            .is_some_and(|ext| ext == "rs" || ext == "toml" || ext == "lock")
        {
            out.push(path);
        }
    }
}

#[derive(Serialize, Deserialize)]
struct PackageWire {
    unit: String,
    entry: PathBuf,
    budget: Option<u64>,
    #[serde(default)]
    opt_stack_promote: bool,
    #[serde(default)]
    opt_level: crate::OptLevel,
    files: Vec<(PathBuf, Vec<u8>)>,
}

impl PackageWire {
    fn from_package(package: &VirtualPackage, options: CompileOptions) -> Self {
        let unit = match package.unit {
            Unit::Bin => "bin",
            Unit::Decl => "decl",
            Unit::Lib => "lib",
            Unit::Snippet => "snippet",
        };
        Self {
            unit: unit.into(),
            entry: package.entry.clone(),
            budget: package.budget,
            opt_stack_promote: options.opt_stack_promote,
            opt_level: options.opt_level,
            files: package
                .files
                .iter()
                .map(|(path, file)| (path.clone(), file.bytes.clone()))
                .collect(),
        }
    }

    fn into_package(self) -> Result<VirtualPackage> {
        let mut package = VirtualPackage::new(self.unit.parse().map_err(failure)?);
        package.entry = self.entry;
        package.budget = self.budget;
        for (path, data) in self.files {
            package.insert(path, data);
        }
        Ok(package)
    }
}
