//! AOT object emission for the initial native MIR probe subset.
use cranelift_codegen::{
    ir::{AbiParam, InstBuilder, types},
    isa,
    settings::{self, Configurable},
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{Linkage, Module, default_libcall_names};
use cranelift_object::{ObjectBuilder, ObjectModule};
use ril_codegen::target::TargetSpec;
use ril_codegen::{BackendError, NativeBackend, ObjectArtifact};
use ril_ir::native::{Body, Module as NativeModule};
use std::collections::HashSet;

pub struct CraneliftBackend;

fn codegen(error: impl std::fmt::Display) -> BackendError {
    BackendError::Codegen(error.to_string())
}

impl NativeBackend for CraneliftBackend {
    fn emit(
        &self,
        input: &NativeModule,
        target: &TargetSpec,
    ) -> Result<ObjectArtifact, BackendError> {
        target
            .validate()
            .map_err(|e| BackendError::Target(e.to_string()))?;
        if input.functions.is_empty() {
            return Err(BackendError::InvalidIr("empty module".into()));
        }
        let mut names = HashSet::new();
        for function in &input.functions {
            let name = &function.symbol;
            if name.is_empty() || name.contains('\0') || !names.insert(name) {
                return Err(BackendError::InvalidIr(format!(
                    "invalid or duplicate symbol: {name:?}"
                )));
            }
        }
        let triple = target
            .triple
            .parse::<target_lexicon::Triple>()
            .map_err(codegen)?;
        let mut flags = settings::builder();
        flags.set("is_pic", "true").map_err(codegen)?;
        let isa = isa::lookup(triple)
            .map_err(codegen)?
            .finish(settings::Flags::new(flags))
            .map_err(codegen)?;
        let builder = ObjectBuilder::new(isa, "ril", default_libcall_names()).map_err(codegen)?;
        let mut module = ObjectModule::new(builder);
        for function in &input.functions {
            let mut signature = module.make_signature();
            signature.returns.push(AbiParam::new(types::I64));
            let id = module
                .declare_function(&function.symbol, Linkage::Export, &signature)
                .map_err(codegen)?;
            let mut context = module.make_context();
            context.func.signature = signature;
            let mut frontend = FunctionBuilderContext::new();
            let mut builder = FunctionBuilder::new(&mut context.func, &mut frontend);
            let entry = builder.create_block();
            builder.switch_to_block(entry);
            builder.seal_all_blocks();
            match function.body {
                Body::ReturnI64(value) => {
                    let value = builder.ins().iconst(types::I64, value);
                    builder.ins().return_(&[value]);
                }
            }
            builder.finalize(module.isa().frontend_config());
            module.define_function(id, &mut context).map_err(codegen)?;
        }
        let bytes = module.finish().emit().map_err(codegen)?;
        Ok(ObjectArtifact {
            target: target.clone(),
            format: target.object_format,
            bytes,
            runtime_contract_version: ril_runtime_api::CONTRACT_VERSION,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use object::{Object, ObjectSymbol};
    use ril_ir::native::Function;
    #[test]
    fn emits_real_x64_coff_and_elf_objects() {
        let input = NativeModule {
            functions: vec![Function {
                symbol: "ril_probe".into(),
                body: Body::ReturnI64(42),
            }],
        };
        for triple in ril_codegen::target::NATIVE_TARGETS {
            let target = TargetSpec::native(triple).unwrap();
            let artifact = CraneliftBackend.emit(&input, &target).unwrap();
            let object = object::File::parse(artifact.bytes.as_slice()).unwrap();
            assert_eq!(object.architecture(), object::Architecture::X86_64);
            assert_eq!(
                object.format(),
                match target.object_format {
                    ril_codegen::target::ObjectFormat::Coff => object::BinaryFormat::Coff,
                    ril_codegen::target::ObjectFormat::Elf => object::BinaryFormat::Elf,
                }
            );
            assert!(
                object
                    .symbols()
                    .any(|symbol| symbol.name() == Ok("ril_probe") && symbol.is_definition())
            );
        }
    }
    #[test]
    fn rejects_empty_or_duplicate_modules() {
        let target = TargetSpec::native(ril_codegen::target::NATIVE_TARGETS[0]).unwrap();
        assert!(
            CraneliftBackend
                .emit(&NativeModule { functions: vec![] }, &target)
                .is_err()
        );
        let function = Function {
            symbol: "duplicate".into(),
            body: Body::ReturnI64(0),
        };
        assert!(
            CraneliftBackend
                .emit(
                    &NativeModule {
                        functions: vec![function.clone(), function]
                    },
                    &target
                )
                .is_err()
        );
    }
}
