use std::{
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::Arc,
};

use ril_backend::{cranelift, mir};
use ril_base::diag::Diagnostic;
use ril_test::{ExecOutput, Unit, VirtualPackage, run_worker};
use serde::{Deserialize, Serialize};

use crate::{CompileOptions, Compiler, Driver, incremental::MirKey};

type Result<T> = std::result::Result<T, Vec<Diagnostic>>;

fn failure(error: impl ToString) -> Vec<Diagnostic> {
    vec![Diagnostic::unsupported(error.to_string())]
}

impl Compiler {
    pub fn lower(&self, package: &VirtualPackage) -> Result<mir::Program> {
        let (typed, analysis, _) = self.analyze_arc(package)?;
        mir::lower_with_options(&typed, &analysis, self.options().lower_options())
            .map_err(|error| vec![error])
    }

    pub fn lower_arc(&self, package: &VirtualPackage) -> Result<Arc<mir::Program>> {
        let (typed, analysis, access) = self.analyze_arc(package)?;
        let key = MirKey {
            access,
            options: self.options(),
        };
        self.lower_with(typed, analysis, key)
    }

    pub fn clif(&self, package: &VirtualPackage) -> Result<String> {
        let (typed, analysis, access) = self.analyze_arc(package)?;
        let key = MirKey {
            access,
            options: self.options(),
        };
        if let Some(cache) = self.cache()
            && let Some(hit) = cache.get_clif(&key)
        {
            return hit.map(|text| (*text).clone());
        }
        let compiled = self.lower_with(typed, analysis, key.clone())?;
        let result = cranelift::emit_clif(&compiled)
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
            cranelift::object(&compiled)
                .map(Arc::new)
                .map_err(|err| vec![err])
        })();
        if let Some(cache) = self.cache() {
            cache.put_object(key, result.clone());
        }
        result
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
        let links = links
            .iter()
            .map(|path| {
                path.canonicalize()
                    .map_err(|err| failure(format!("{}: {err}", path.display())))
            })
            .collect::<Result<Vec<_>>>()?;
        let object = self.compile_object(package)?;
        link_object(&object, &links, output)
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
        };
        let package = wire.into_package()?;
        let program = self.with_options(options).lower(&package)?;
        cranelift::jit(&program).map_err(|err| vec![err])
    }
}

pub(crate) fn link_object(object: &[u8], links: &[PathBuf], output: &Path) -> Result<()> {
    let tmp = tempfile::tempdir().map_err(failure)?;
    let object_path = tmp.path().join("ril.o");
    fs::write(&object_path, object).map_err(failure)?;
    let runtime = runtime_archive()?;
    let mut command = Command::new(std::env::var_os("CC").unwrap_or_else(|| "cc".into()));
    command.arg(&object_path).args(links).arg(runtime);
    if cfg!(target_os = "linux") {
        command.args(["-ldl", "-lpthread", "-lm"]);
    }
    let link = command.arg("-o").arg(output).output().map_err(failure)?;
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
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
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
    Ok(target.join("release").join(if cfg!(target_env = "msvc") {
        "ril_rt.lib"
    } else {
        "libril_rt.a"
    }))
}

#[derive(Serialize, Deserialize)]
struct PackageWire {
    unit: String,
    entry: PathBuf,
    budget: Option<u64>,
    #[serde(default)]
    opt_stack_promote: bool,
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
