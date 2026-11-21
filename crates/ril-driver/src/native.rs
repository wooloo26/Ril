use std::{
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use ril_backend::{cranelift, mir};
use ril_base::diag::Diagnostic;
use ril_test::{ExecOutput, Unit, VirtualPackage, run_worker};
use serde::{Deserialize, Serialize};

use crate::Driver;

type Result<T> = std::result::Result<T, Vec<Diagnostic>>;

fn failure(error: impl ToString) -> Vec<Diagnostic> {
    vec![Diagnostic::unsupported(error.to_string())]
}

impl Driver {
    pub fn lower(&self, package: &VirtualPackage) -> Result<mir::Program> {
        let (typed, analysis) = self.analyze(package)?;
        mir::lower(&typed, &analysis).map_err(|error| vec![error])
    }

    pub fn clif(&self, package: &VirtualPackage) -> Result<String> {
        cranelift::emit_clif(&self.lower(package)?).map_err(|err| vec![err])
    }

    pub fn horn_json(&self, package: &VirtualPackage) -> Result<String> {
        let (_, access) = self.analyze(package)?;
        serde_json::to_string_pretty(&access.horn_rules).map_err(failure)
    }

    pub fn compile_aot(&self, package: &VirtualPackage, output: &Path) -> Result<()> {
        let compiled = self.lower(package)?;
        let object = cranelift::object(&compiled).map_err(|err| vec![err])?;
        let tmp = tempfile::tempdir().map_err(failure)?;
        let object_path = tmp.path().join("ril.o");
        fs::write(&object_path, object).map_err(failure)?;
        let runtime = runtime_archive()?;
        let mut command = Command::new(std::env::var_os("CC").unwrap_or_else(|| "cc".into()));
        command.arg(&object_path).arg(runtime);
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

    pub fn execute_jit(&self, package: &VirtualPackage) -> Result<ExecOutput> {
        let executable = std::env::current_exe().map_err(failure)?;
        let temporary = tempfile::NamedTempFile::new().map_err(failure)?;
        let wire = PackageWire::from(package);
        serde_json::to_writer(temporary.as_file(), &wire).map_err(failure)?;
        run_worker(
            Command::new(executable)
                .arg("--__ril_worker")
                .arg(temporary.path()),
        )
        .map_err(failure)
    }

    fn worker(&self, path: &Path) -> Result<i32> {
        let file = fs::File::open(path).map_err(failure)?;
        let wire: PackageWire = serde_json::from_reader(file).map_err(failure)?;
        let package = wire.into_package()?;
        let program = self.lower(&package)?;
        cranelift::jit(&program, &ril_rt_core::symbols()).map_err(|err| vec![err])
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
    files: Vec<(PathBuf, Vec<u8>)>,
}

impl From<&VirtualPackage> for PackageWire {
    fn from(package: &VirtualPackage) -> Self {
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
            files: package
                .files
                .iter()
                .map(|(path, file)| (path.clone(), file.bytes.clone()))
                .collect(),
        }
    }
}

impl PackageWire {
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
