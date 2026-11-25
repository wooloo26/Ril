use std::collections::BTreeMap;

use cranelift_codegen::{
    ir::{self, AbiParam, InstBuilder as _, Value, types},
    verify_function,
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{FuncId, Linkage, Module};
use ril_mir::{FunctionId, Register};

use super::{MirToClifTranslator, RIL_UNIT, Result, diagnostic};

impl<M: Module> MirToClifTranslator<'_, M> {
    pub(super) fn function_id(&self, id: FunctionId) -> Result<FuncId> {
        self.functions
            .get(id.0)
            .copied()
            .ok_or_else(|| diagnostic("invalid MIR function ID"))
    }

    pub(super) fn signature(&self, count: usize, output: Option<ir::Type>) -> ir::Signature {
        let mut signature = self.module.make_signature();
        signature
            .params
            .extend((0..count).map(|_| AbiParam::new(types::I64)));
        signature.returns.extend(output.map(AbiParam::new));
        signature
    }

    pub(super) fn import(
        &mut self,
        name: &str,
        count: usize,
        output: Option<ir::Type>,
    ) -> Result<FuncId> {
        let signature = self.signature(count, output);
        self.module
            .declare_function(name, Linkage::Import, &signature)
            .map_err(diagnostic)
    }

    pub(super) fn call(
        &mut self,
        builder: &mut FunctionBuilder<'_>,
        id: FuncId,
        args: &[Value],
    ) -> Option<Value> {
        let reference = self.module.declare_func_in_func(id, builder.func);
        let call = builder.ins().call(reference, args);
        builder.inst_results(call).first().copied()
    }

    pub(super) fn native(
        &mut self,
        builder: &mut FunctionBuilder<'_>,
        name: &str,
        params: &[Value],
        result: Option<ir::Type>,
    ) -> Result<Option<Value>> {
        let function = self.import(name, params.len(), result)?;
        Ok(self.call(builder, function, params))
    }

    pub(super) fn handle(
        &mut self,
        builder: &mut FunctionBuilder<'_>,
        name: &str,
        args: &[Value],
    ) -> Result<Value> {
        self.native(builder, name, args, Some(types::I64))?
            .ok_or_else(|| diagnostic("runtime function has no return value"))
    }

    pub(super) fn wrapper(
        &mut self,
        entry: FunctionId,
        suspend_at_entry: bool,
    ) -> Result<(FuncId, String)> {
        let mut context = self.module.make_context();
        context.func.signature = self.signature(0, Some(types::I32));
        let id = self
            .module
            .declare_function("main", Linkage::Export, &context.func.signature)
            .map_err(diagnostic)?;
        let mut scratch = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut context.func, &mut scratch);
        let block = builder.create_block();
        builder.switch_to_block(block);
        let rt = self.handle(&mut builder, "ril_rt_create", &[])?;
        let null = builder.ins().iconst(types::I64, RIL_UNIT);
        let function = self.function_id(entry)?;
        let value = if suspend_at_entry {
            let entry = self.module.declare_func_in_func(function, builder.func);
            let address = builder.ins().func_addr(types::I64, entry);
            let closure = self.handle(
                &mut builder,
                "ril_rt_closure",
                &[rt, address, null, null, null],
            )?;
            self.handle(&mut builder, "ril_fiber_run", &[rt, closure])?
        } else {
            self.call(&mut builder, function, &[rt, null, null])
                .ok_or_else(|| diagnostic("entry has no return value"))?
        };
        let exit = self
            .native(
                &mut builder,
                "ril_rt_finish",
                &[rt, value],
                Some(types::I32),
            )?
            .ok_or_else(|| diagnostic("runtime finish must return status"))?;
        builder.ins().return_(&[exit]);
        builder.seal_block(block);
        builder.finalize(self.module.target_config());
        if cfg!(debug_assertions) {
            verify_function(&context.func, self.module.isa()).map_err(diagnostic)?;
        }
        let text = if self.emit_text {
            context.func.display().to_string()
        } else {
            String::new()
        };
        self.module
            .define_function(id, &mut context)
            .map_err(diagnostic)?;
        Ok((id, text))
    }
}

pub(super) fn reg(registers: &BTreeMap<Register, Value>, register: Register) -> Result<Value> {
    registers
        .get(&register)
        .copied()
        .ok_or_else(|| diagnostic(format!("undefined MIR register {}", register.0)))
}

pub(super) fn number(builder: &mut FunctionBuilder<'_>, value: usize) -> Result<Value> {
    let value = i64::try_from(value).map_err(diagnostic)?;
    Ok(builder.ins().iconst(types::I64, value))
}
