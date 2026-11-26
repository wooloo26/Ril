mod abi;
mod liveness;
mod translate;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use cranelift_codegen::{
    ir::types,
    isa,
    settings::{self, Configurable as _},
};
use cranelift_module::{DataId, FuncId, Linkage, Module, default_libcall_names};
use cranelift_object::{ObjectBuilder, ObjectModule};
use ril_source::diag::Diagnostic;

use ril_mir::{self, ForeignImport, FunctionId, Target, Terminator};

use self::liveness::reachable;

type Result<T> = std::result::Result<T, Diagnostic>;

const RIL_UNIT: i64 = 0;
const RIL_FALSE: i64 = 0b010;
const RIL_TRUE: i64 = 0b110;

/// Cranelift backend optimization level exposed to `ril build` / `ril run`.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub enum OptLevel {
    #[default]
    None,
    Speed,
    SpeedAndSize,
}

impl OptLevel {
    const fn as_cranelift(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::Speed => "speed",
            Self::SpeedAndSize => "speed_and_size",
        }
    }
}

fn diagnostic(error: impl std::fmt::Display) -> Diagnostic {
    Diagnostic::unsupported(format!("native code generation: {error}"))
}

fn target(pic: bool, opt_level: OptLevel) -> Result<isa::OwnedTargetIsa> {
    let mut flags = settings::builder();
    flags
        .set("is_pic", if pic { "true" } else { "false" })
        .map_err(diagnostic)?;
    flags
        .set("opt_level", opt_level.as_cranelift())
        .map_err(diagnostic)?;
    flags.set("unwind_info", "true").map_err(diagnostic)?;
    flags
        .set(
            "enable_verifier",
            if cfg!(debug_assertions) {
                "true"
            } else {
                "false"
            },
        )
        .map_err(diagnostic)?;
    let isa = cranelift_native::builder()
        .map_err(diagnostic)?
        .finish(settings::Flags::new(flags))
        .map_err(diagnostic)?;
    if isa.pointer_type() != types::I64 {
        return Err(diagnostic(
            "the Ril native ABI requires a 64-bit host target",
        ));
    }
    Ok(isa)
}

pub fn object(program: &ril_mir::Program) -> Result<Vec<u8>> {
    object_with_opt(program, OptLevel::None)
}

pub fn object_with_opt(program: &ril_mir::Program, opt_level: OptLevel) -> Result<Vec<u8>> {
    let mut object = ObjectBuilder::new(
        target(true, opt_level)?,
        "ril.program",
        default_libcall_names(),
    )
    .map_err(diagnostic)?;
    object.unwind_info(!cfg!(target_os = "macos"));
    let mut module = ObjectModule::new(object);
    MirToClifTranslator::compile(&mut module, program, None, false)?;
    module.finish().emit().map_err(diagnostic)
}

/// Compile a MIR program into `cgu_count` single-owner object files using deterministic
/// canonical symbol partitioning (`Linkage::Export` in the owning CGU, `Linkage::Import`
/// in all other CGUs). The executable `main` wrapper is emitted in CGU 0.
pub fn objects_with_opt(
    program: &ril_mir::Program,
    cgu_count: usize,
    opt_level: OptLevel,
) -> Result<Vec<Vec<u8>>> {
    let count = cgu_count.max(1).min(program.functions.len().max(1));
    if count <= 1 {
        return Ok(vec![object_with_opt(program, opt_level)?]);
    }
    let owners: Vec<usize> = program
        .functions
        .iter()
        .enumerate()
        .map(|(idx, function)| {
            if FunctionId(idx) == program.entry {
                0
            } else {
                let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
                for &b in function.symbol.as_bytes() {
                    hash ^= u64::from(b);
                    hash = hash.wrapping_mul(0x0100_0000_01b3);
                }
                usize::try_from(hash % (count as u64)).unwrap_or(0)
            }
        })
        .collect();
    let mut objects = Vec::with_capacity(count);
    for cgu in 0..count {
        let name = format!("ril.cgu.{cgu}");
        let mut object =
            ObjectBuilder::new(target(true, opt_level)?, name, default_libcall_names())
                .map_err(diagnostic)?;
        object.unwind_info(!cfg!(target_os = "macos"));
        let mut module = ObjectModule::new(object);
        MirToClifTranslator::compile_cgu(&mut module, program, &owners, cgu)?;
        objects.push(module.finish().emit().map_err(diagnostic)?);
    }
    Ok(objects)
}

pub fn emit_clif(program: &ril_mir::Program) -> Result<String> {
    emit_clif_with_opt(program, OptLevel::None)
}

pub fn emit_clif_with_opt(program: &ril_mir::Program, opt_level: OptLevel) -> Result<String> {
    let object = ObjectBuilder::new(
        target(true, opt_level)?,
        "ril.program",
        default_libcall_names(),
    )
    .map_err(diagnostic)?;
    let mut module = ObjectModule::new(object);
    let (_, text) = MirToClifTranslator::compile(&mut module, program, None, true)?;
    Ok(text)
}

#[cfg(feature = "native-runtime")]
#[allow(
    unsafe_code,
    reason = "execute the verified native entry while its JIT module owns the code"
)]
pub fn jit(program: &ril_mir::Program) -> Result<i32> {
    // SAFETY: the resolver supplies no host functions. Every reachable import
    // outside the runtime must resolve explicitly before generated code is run.
    unsafe { jit_with_imports_and_opt(program, OptLevel::None, |_| None) }
}

#[cfg(feature = "native-runtime")]
#[allow(
    unsafe_code,
    reason = "execute the verified native entry while its JIT module owns the code"
)]
pub fn jit_with_opt(program: &ril_mir::Program, opt_level: OptLevel) -> Result<i32> {
    // SAFETY: the resolver supplies no host functions. Every reachable import
    // outside the runtime must resolve explicitly before generated code is run.
    unsafe { jit_with_imports_and_opt(program, opt_level, |_| None) }
}

/// Execute native code with an embedding application's host bindings.
///
/// # Safety
/// Each resolved address must remain executable throughout the call and point
/// to a C-ABI function that takes the runtime context pointer followed by the
/// declared number of Ril value words (`u64`), and returns one Ril value word.
/// A constant uses an accessor that takes only the context pointer. Each
/// binding must honor the value, resource, and effect contracts of its
/// declaration and must never unwind across the C ABI.
#[cfg(feature = "native-runtime")]
#[allow(
    unsafe_code,
    reason = "verify imports before entering generated native code"
)]
pub unsafe fn jit_with_imports(
    program: &ril_mir::Program,
    resolve: impl FnMut(&ForeignImport) -> Option<*const u8>,
) -> Result<i32> {
    // SAFETY: caller upholds the foreign import ABI contract.
    unsafe { jit_with_imports_and_opt(program, OptLevel::None, resolve) }
}

/// Execute native code at a chosen Cranelift optimization level with host bindings.
///
/// # Safety
/// Same requirements as [`jit_with_imports`].
#[cfg(feature = "native-runtime")]
#[allow(
    unsafe_code,
    reason = "verify imports before entering generated native code"
)]
pub unsafe fn jit_with_imports_and_opt(
    program: &ril_mir::Program,
    opt_level: OptLevel,
    mut resolve: impl FnMut(&ForeignImport) -> Option<*const u8>,
) -> Result<i32> {
    use cranelift_jit::{JITBuilder, JITModule};

    let mut builder = JITBuilder::with_isa(target(false, opt_level)?, default_libcall_names());
    builder.symbols(ril_rt::symbols());
    let mut imports = BTreeSet::new();
    for function in &program.functions {
        for id in reachable(function)? {
            let block = function
                .blocks
                .get(id.0)
                .ok_or_else(|| diagnostic("invalid foreign import block"))?;
            if let Some(Terminator::Invoke {
                target: Target::Foreign(import),
                ..
            }) = &block.terminator
            {
                imports.insert(import.as_ref());
            }
        }
    }
    let mut foreign_names = BTreeMap::new();
    for (ordinal, import) in imports.into_iter().enumerate() {
        let address = resolve(import)
            .filter(|address| !address.is_null())
            .ok_or_else(|| {
                diagnostic(format!(
                    "unregistered foreign JIT import {}",
                    import.declaration
                ))
            })?;
        // Use a private alias outside the runtime's symbol namespace.
        let alias = format!("ril_host_{ordinal}");
        builder.symbol(&alias, address);
        foreign_names.insert(import.clone(), alias);
    }
    let mut module = JITModule::new(builder);
    let (entry, _) =
        MirToClifTranslator::compile(&mut module, program, Some(&foreign_names), false)?;
    module.finalize_definitions().map_err(diagnostic)?;
    let address = module.get_finalized_function(entry);
    // SAFETY: the translator defines entry with the platform C signature () -> i32.
    // Runtime imports are bound to the linked Ril ABI, the caller vouches for
    // each host import, and the JIT module stays alive during execution.
    let execute = unsafe { std::mem::transmute::<*const u8, extern "C" fn() -> i32>(address) };
    Ok(execute())
}

struct MirToClifTranslator<'a, M> {
    module: &'a mut M,
    functions: Vec<FuncId>,
    foreign_names: Option<&'a BTreeMap<ForeignImport, String>>,
    data_pool: HashMap<Box<[u8]>, DataId>,
    emit_text: bool,
}

fn foreign_symbol<'a>(
    names: Option<&'a BTreeMap<ForeignImport, String>>,
    import: &'a ForeignImport,
) -> Result<&'a str> {
    match names {
        Some(names) => names
            .get(import)
            .map(String::as_str)
            .ok_or_else(|| diagnostic("missing checked foreign JIT binding")),
        None => Ok(&import.symbol),
    }
}

impl<'a, M: Module> MirToClifTranslator<'a, M> {
    fn compile(
        module: &'a mut M,
        program: &ril_mir::Program,
        foreign_names: Option<&'a BTreeMap<ForeignImport, String>>,
        emit_text: bool,
    ) -> Result<(FuncId, String)> {
        let (entry, ir) = Self::compile_unit(module, program, None, foreign_names, emit_text)?;
        let entry = entry.ok_or_else(|| diagnostic("missing executable entry wrapper"))?;
        Ok((entry, ir))
    }

    fn compile_cgu(
        module: &'a mut M,
        program: &ril_mir::Program,
        owners: &[usize],
        cgu: usize,
    ) -> Result<()> {
        let _ = Self::compile_unit(module, program, Some((owners, cgu)), None, false)?;
        Ok(())
    }

    fn compile_unit(
        module: &'a mut M,
        program: &ril_mir::Program,
        cgu_partition: Option<(&[usize], usize)>,
        foreign_names: Option<&'a BTreeMap<ForeignImport, String>>,
        emit_text: bool,
    ) -> Result<(Option<FuncId>, String)> {
        let mut compiler = MirToClifTranslator {
            module,
            functions: Vec::new(),
            foreign_names,
            data_pool: HashMap::new(),
            emit_text,
        };
        let owned = |index: usize| {
            cgu_partition.is_none_or(|(owners, cgu)| owners.get(index).copied() == Some(cgu))
        };
        for (index, function) in program.functions.iter().enumerate() {
            let signature = compiler.signature(function.arity + 2, Some(types::I64));
            let linkage = match cgu_partition {
                None => Linkage::Local,
                Some(_) if owned(index) => Linkage::Export,
                Some(_) => Linkage::Import,
            };
            let id = compiler
                .module
                .declare_function(&function.symbol, linkage, &signature)
                .map_err(diagnostic)?;
            compiler.functions.push(id);
        }
        let mut ir = String::new();
        for (index, function) in program.functions.iter().enumerate() {
            if !owned(index) {
                continue;
            }
            let id = compiler.function_id(FunctionId(index))?;
            let code = compiler.translate(id, function)?;
            if emit_text {
                use std::fmt::Write as _;
                writeln!(
                    ir,
                    "\n; {}\n; symbol: {}\n{code}",
                    function.name, function.symbol
                )
                .map_err(diagnostic)?;
            }
        }
        let entry = if cgu_partition.is_none_or(|(_, cgu)| cgu == 0) {
            let (entry, wrapper) = compiler.wrapper(program.entry)?;
            if emit_text {
                use std::fmt::Write as _;
                writeln!(ir, "\n; executable entry\n{wrapper}").map_err(diagnostic)?;
            }
            Some(entry)
        } else {
            None
        };
        Ok((entry, ir))
    }
}

#[cfg(all(test, feature = "native-runtime"))]
mod tests {
    use std::sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    };

    use ril_mir::{BlockId, ForeignAbi, Instruction, Register};

    use super::*;

    #[test]
    #[allow(unsafe_code, reason = "exercise a host function with a known C ABI")]
    fn explicitly_bound_host_import_executes_without_process_symbol_lookup() {
        static OBSERVED: AtomicU64 = AtomicU64::new(0);
        extern "C" fn enabled(_context: *mut std::ffi::c_void) -> u64 {
            6
        }
        extern "C" fn host(_context: *mut std::ffi::c_void, value: u64) -> u64 {
            OBSERVED.store(value, Ordering::Relaxed);
            0
        }
        let import = Arc::new(ForeignImport {
            declaration: "pkg/host.d.ril::record".into(),
            symbol: "record".into(),
            signature: "fn(value: bool) @io -> ()".into(),
            abi: ForeignAbi::Function { arity: 1 },
        });
        let constant = Arc::new(ForeignImport {
            declaration: "pkg/host.d.ril::enabled".into(),
            symbol: "enabled".into(),
            signature: "bool".into(),
            abi: ForeignAbi::Constant,
        });
        let program = ril_mir::Program {
            entry: FunctionId(0),
            source_locs: Vec::new(),
            functions: vec![ril_mir::Function {
                name: "main".into(),
                symbol: "_Ril_main_test".into(),
                source_loc: None,
                arity: 0,
                registers: 3,
                reg_types: vec![
                    ril_mir::MirTy::Bool,
                    ril_mir::MirTy::Unit,
                    ril_mir::MirTy::Unit,
                ],
                stack_slots: 0,
                blocks: vec![
                    ril_mir::Block {
                        params: Vec::new(),
                        instructions: vec![(Register(1), Instruction::Handle(0))],
                        terminator: Some(Terminator::Invoke {
                            target: Target::Foreign(Arc::clone(&constant)),
                            arguments: Vec::new(),
                            normal: BlockId(1),
                            unwind: BlockId(3),
                            cleanup: false,
                            keep_result: true,
                        }),
                    },
                    ril_mir::Block {
                        params: vec![Register(0)],
                        terminator: Some(Terminator::Invoke {
                            target: Target::Foreign(Arc::clone(&import)),
                            arguments: vec![Register(0)],
                            normal: BlockId(2),
                            unwind: BlockId(3),
                            cleanup: false,
                            keep_result: true,
                        }),
                        ..ril_mir::Block::default()
                    },
                    ril_mir::Block {
                        params: vec![Register(2)],
                        terminator: Some(Terminator::Return(Register(2))),
                        ..ril_mir::Block::default()
                    },
                    ril_mir::Block {
                        terminator: Some(Terminator::Return(Register(1))),
                        ..ril_mir::Block::default()
                    },
                ],
            }],
        };
        assert!(jit(&program).is_err());
        // SAFETY: host has the declared null-unwind C ABI, accepts a packed bool,
        // and returns the unit word. enabled always returns the Ril true word.
        let exit = unsafe {
            jit_with_imports(&program, |request| {
                if request == import.as_ref() {
                    Some(host as *const u8)
                } else {
                    (request == constant.as_ref()).then_some(enabled as *const u8)
                }
            })
        }
        .unwrap();
        assert_eq!(exit, 0);
        assert_eq!(OBSERVED.load(Ordering::Relaxed), 6);
    }
}
