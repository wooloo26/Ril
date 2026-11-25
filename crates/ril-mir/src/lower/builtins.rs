use std::collections::BTreeMap;

use ril_sema::{
    hir::{DefinitionId, Intrinsic},
    syntax::{Argument, ExprId},
    ty::Ty,
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
            self.traps.push((self.cleanups.len(), abort));
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
                    evidence: self.evidence,
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
            let wrapper = self.collection(arg.value)?;
            return Ok(
                match self
                    .global
                    .typed
                    .types
                    .get(&span)
                    .map(|ty| self.concrete(ty))
                {
                    Some(Ty::Unit) => self.unit(),
                    Some(Ty::Record(..)) => wrapper,
                    Some(Ty::Tuple(_)) if arg.mode == ril_sema::syntax::Mode::Mut => wrapper,
                    Some(Ty::Tuple(parts)) => {
                        let tuple = self.runtime("ril_rt_tuple", Vec::new());
                        for index in 0..parts.len() {
                            let key = self.integer(&index.to_string());
                            let value = self.runtime("ril_rt_load", vec![wrapper, key]);
                            self.runtime("ril_rt_append", vec![tuple, value]);
                        }
                        tuple
                    }
                    _ => {
                        let key = self.integer("0");
                        self.runtime("ril_rt_load", vec![wrapper, key])
                    }
                },
            );
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
            let mut value = self.collection(argument.value)?;
            let arg_span = self.ast().expr(argument.value).span;
            let is_set = self
                .global
                .typed
                .types
                .get(&arg_span)
                .map(|ty| self.concrete(ty))
                .is_some_and(|ty| match ty {
                    Ty::Draft(inner) => inner.is_set(&self.global.typed.hir),
                    other => other.is_set(&self.global.typed.hir),
                });
            if is_set {
                let zero = self.integer("0");
                value = self.runtime("ril_rt_load", vec![value, zero]);
            }
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
        let symbol = if self.global.typed.hir.primitive_module(id) == Some("Fiber")
            && name == "join"
            && args
                .get(1)
                .is_some_and(|arg| arg.mode == ril_sema::syntax::Mode::New)
        {
            "ril_fiber_join_owned"
        } else if let Some(symbol) = self.global.typed.hir.runtime_symbol(id) {
            symbol
        } else {
            return Err(self.unsupported(span, &format!("primitive {name}")));
        };
        Ok(self.runtime(symbol, values))
    }

    fn absorb(&mut self, action: ExprId, span: Span) -> Result<Register> {
        let action = self.expr(action)?;
        let caught = self.block(0);
        let join = self.block(1);
        self.traps.push((self.cleanups.len(), caught));
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
