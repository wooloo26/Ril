use std::collections::BTreeMap;

use ril_sema::{
    hir::{DefinitionId, Intrinsic},
    syntax::{Argument, ExprId},
};
use ril_source::span::Span;

use super::{Builder, Result};
use crate::{DraftOp, Register, Target, Terminator};

impl Builder<'_, '_> {
    pub(super) fn primitive(
        &mut self,
        id: DefinitionId,
        name: &str,
        args: &[Argument],
        span: Span,
    ) -> Result<Register> {
        let intrinsic = self.global.typed.hir.intrinsic(id);
        if intrinsic == Some(Intrinsic::WithScoped)
            && let [value, body] = args
        {
            let v = self.expr(value.value)?;
            let b = self.expr(body.value)?;
            return Ok(self.invoke_closure(b, vec![v]));
        }
        if intrinsic == Some(Intrinsic::RecoverPanic)
            && let [action] = args
        {
            return self.absorb(action.value, span);
        }
        if intrinsic == Some(Intrinsic::Derive)
            && let [base, update] = args
        {
            let base = self.expr(base.value)?;
            let draft = self.draft(DraftOp::Begin, vec![base]);
            let abort = self.block(0);
            let done = self.block(1);
            self.traps.push((self.scopes.len(), abort));
            let callback = self.expr(update.value)?;
            self.invoke_closure(callback, vec![draft]);
            self.traps.pop();
            let result = self.draft(DraftOp::Commit, vec![draft]);
            self.terminate(Terminator::Jump(done, vec![result]));
            self.current = Some(abort);
            let outer_unwind = self.unwind_pad();
            self.term_at(
                abort,
                Terminator::Invoke {
                    target: Target::Draft(DraftOp::Abort),
                    arguments: vec![draft],
                    normal: outer_unwind,
                    unwind: outer_unwind,
                    cleanup: true,
                    keep_result: false,
                },
            );
            self.current = Some(done);
            return Ok(self.result_param(done));
        }
        if intrinsic == Some(Intrinsic::Inner)
            && let [arg] = args
        {
            return self.expr(arg.value);
        }
        if intrinsic == Some(Intrinsic::StringInspect)
            && let [argument] = args
        {
            let argument_span = self.ast().expr(argument.value).span;
            let value = self.expr(argument.value)?;
            if let Some(plan) = self
                .global
                .typed
                .inspection_plan(span, argument_span, &self.types)
            {
                let plan = self.constant(&plan, span)?;
                return Ok(self.runtime("ril_rt_inspect_typed", vec![value, plan]));
            }
            return Ok(self.runtime("ril_rt_inspect", vec![value]));
        }
        if intrinsic == Some(Intrinsic::Len)
            && let [argument] = args
        {
            let value = self.collection(argument.value)?;
            return Ok(self.runtime("ril_rt_len", vec![value]));
        }
        if matches!(
            intrinsic,
            Some(Intrinsic::AsyncJoin | Intrinsic::AsyncTryJoin)
        ) && let [tasks_arg] = args
        {
            let is_try = intrinsic == Some(Intrinsic::AsyncTryJoin);
            let tasks_span = self.ast().expr(tasks_arg.value).span;
            let tasks_ty = self
                .global
                .typed
                .types
                .get(&tasks_span)
                .map(|t| self.concrete(t))
                .unwrap_or(ril_sema::ty::Ty::Unknown);
            let field_names: Vec<String> = match tasks_ty {
                ril_sema::ty::Ty::Record(fields, _) => fields.keys().cloned().collect(),
                _ => {
                    return Err(self.unsupported(
                        span,
                        "Async::join requires a concrete record of task thunks",
                    ));
                }
            };
            let tasks_reg = self.expr(tasks_arg.value)?;
            let thunks = self.runtime("ril_rt_array", Vec::new());
            for field in &field_names {
                let key = self.string(field);
                let thunk = self.runtime("ril_rt_load", vec![tasks_reg, key]);
                self.runtime("ril_rt_append", vec![thunks, thunk]);
            }
            let helper_name = if is_try {
                "_try_join_array"
            } else {
                "_join_array"
            };
            let async_file = self.global.typed.hir.definition(id).name.span.file;
            let helper_id = self
                .global
                .typed
                .hir
                .definitions()
                .find(|(_, d)| d.name.value == helper_name && d.name.span.file == async_file)
                .map(|(hid, _)| hid)
                .ok_or_else(|| self.unsupported(span, "missing Async join helper"))?;
            let helper_fn = self.global.queue(super::Work::Named(
                helper_id,
                BTreeMap::new(),
                Vec::new(),
                BTreeMap::new(),
            ));
            let helper_out = self.invoke(Target::Function(helper_fn), vec![thunks], false);
            if !is_try {
                let record = self.runtime("ril_rt_record", Vec::new());
                for (idx, field) in field_names.iter().enumerate() {
                    let idx_reg = self.integer(&idx.to_string());
                    let val = self.runtime("ril_rt_load", vec![helper_out, idx_reg]);
                    let key = self.string(field);
                    self.runtime("ril_rt_store", vec![record, key, val]);
                }
                return Ok(record);
            }
            let ok_bb = self.block(0);
            let err_bb = self.block(0);
            let done_bb = self.block(1);
            let ok_tag = self.string("Ok");
            let is_ok = self.runtime("ril_rt_is_tag", vec![helper_out, ok_tag]);
            self.terminate(Terminator::Branch {
                condition: is_ok,
                yes: ok_bb,
                no: err_bb,
            });
            self.current = Some(ok_bb);
            let zero = self.integer("0");
            let arr = self.runtime("ril_rt_load", vec![helper_out, zero]);
            let record = self.runtime("ril_rt_record", Vec::new());
            for (idx, field) in field_names.iter().enumerate() {
                let idx_reg = self.integer(&idx.to_string());
                let val = self.runtime("ril_rt_load", vec![arr, idx_reg]);
                let key = self.string(field);
                self.runtime("ril_rt_store", vec![record, key, val]);
            }
            let ok_rec = self.tag("Ok", vec![record]);
            self.terminate(Terminator::Jump(done_bb, vec![ok_rec]));
            self.current = Some(err_bb);
            self.terminate(Terminator::Jump(done_bb, vec![helper_out]));
            self.current = Some(done_bb);
            return Ok(self.result_param(done_bb));
        }
        let values = if let Some(decl) = self.global.declaration(id) {
            self.arguments(
                &decl.signature.params,
                decl.name.span.file,
                args,
                &BTreeMap::new(),
                span,
            )?
        } else {
            args.iter()
                .map(|arg| self.expr(arg.value))
                .collect::<Result<Vec<_>>>()?
        };
        let Some(symbol) = self.global.typed.hir.runtime_symbol(id) else {
            return Err(self.unsupported(span, &format!("primitive {name}")));
        };
        Ok(self.runtime(symbol, values))
    }

    fn absorb(&mut self, action: ExprId, span: Span) -> Result<Register> {
        let action = self.expr(action)?;
        let caught = self.block(0);
        let join = self.block(1);
        self.traps.push((self.scopes.len(), caught));
        let result = self.invoke_closure(action, Vec::new());
        self.traps.pop();
        let ok = self.tag("Ok", vec![result]);
        self.terminate(Terminator::Jump(join, vec![ok]));
        self.current = Some(caught);
        let message = self.runtime("ril_rt_panic_take", Vec::new());
        let info = self.tag("Panicked", vec![message]);
        let error = self.tag("Err", vec![info]);
        self.terminate(Terminator::Jump(join, vec![error]));
        self.current = Some(join);
        self.params(join)
            .first()
            .copied()
            .ok_or_else(|| self.unsupported(span, "panic boundary result"))
    }
}
