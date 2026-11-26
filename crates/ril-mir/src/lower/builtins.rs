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
        if intrinsic == Some(Intrinsic::AbsorbPanic)
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
