use std::collections::{BTreeMap, BTreeSet};

use ril_sema::{
    hir::DefinitionId,
    syntax::{Expr, ExprId, StmtKind},
    ty::Value,
};

use super::{Builder, Result, Work};
use crate::{FunctionId, Instruction, Register, Target};

impl Builder<'_, '_> {
    pub(super) fn named_captures(&self, id: DefinitionId) -> Vec<DefinitionId> {
        self.global
            .declaration(id)
            .into_iter()
            .flat_map(|fun| {
                fun.signature
                    .obligations
                    .state
                    .iter()
                    .filter(|clause| clause.kind == ril_sema::syntax::StateKind::Environment)
                    .flat_map(|clause| &clause.bindings)
            })
            .filter_map(|(_, path)| self.global.resolve(path.span))
            .collect()
    }

    pub(super) fn environment(&mut self, captures: &[DefinitionId]) -> Register {
        if captures.is_empty() {
            return self.unit();
        }
        let environment = self.runtime("ril_rt_tuple", Vec::new());
        for id in captures {
            if let Some(&value) = self.locals.get(id) {
                self.runtime("ril_rt_append", vec![environment, value]);
            }
        }
        environment
    }

    pub(super) fn box_closure(
        &mut self,
        id: FunctionId,
        arity: usize,
        environment: Register,
    ) -> Register {
        let address = self.instruction(Instruction::FunctionAddress(id));
        let arity = self.instruction(Instruction::RawU64(
            u64::try_from(arity).unwrap_or(u64::MAX),
        ));
        self.runtime("ril_rt_closure", vec![address, arity, environment])
    }

    pub(super) fn invoke_closure(&mut self, closure: Register, args: Vec<Register>) -> Register {
        let arity = self.instruction(Instruction::RawU64(
            u64::try_from(args.len()).unwrap_or(u64::MAX),
        ));
        let address = self.runtime("ril_rt_closure_address", vec![closure, arity]);
        let environment = self.runtime("ril_rt_closure_environment", vec![closure]);
        self.invoke(
            Target::Indirect {
                address,
                environment,
            },
            args,
            false,
        )
    }

    pub(super) fn collect_captures_in_spans(
        &self,
        spans: impl IntoIterator<Item = ril_source::span::Span>,
    ) -> Vec<DefinitionId> {
        let mut referenced: Vec<DefinitionId> = spans
            .into_iter()
            .flat_map(|span| self.global.typed.hir.references_within(span))
            .map(|(_, def)| def)
            .collect();
        let mut capture = BTreeSet::new();
        let mut visited_fns = BTreeSet::new();
        while let Some(def) = referenced.pop() {
            if self.locals.contains_key(&def) {
                capture.insert(def);
            } else if visited_fns.insert(def) {
                let info = self.global.typed.hir.definition(def);
                if let Some(stmt_id) = info.stmt {
                    let ast = &self.global.typed.hir.file(info.name.span.file).ast;
                    if let StmtKind::Function(fun) = &ast.stmt(stmt_id).value.kind {
                        for (_, up_path) in fun
                            .signature
                            .obligations
                            .state
                            .iter()
                            .flat_map(|clause| &clause.bindings)
                        {
                            if let Some(up_def) = self.global.resolve(up_path.span) {
                                referenced.push(up_def);
                            }
                        }
                    }
                }
            }
        }
        capture.into_iter().collect()
    }

    pub(super) fn lift(
        &mut self,
        id: ExprId,
        arguments: Option<&BTreeMap<DefinitionId, Value>>,
    ) -> Result<Register> {
        self.lift_with_tail_resume(id, arguments, None)
    }

    pub(super) fn lift_with_tail_resume(
        &mut self,
        id: ExprId,
        arguments: Option<&BTreeMap<DefinitionId, Value>>,
        tail_resume_k: Option<DefinitionId>,
    ) -> Result<Register> {
        let span = self.ast().expr(id).span;
        let capture = self.collect_captures_in_spans(std::iter::once(span));
        let environment = self.environment(&capture);
        let mut statics = self.statics.clone();
        if let Some(arguments) = arguments {
            statics.extend(arguments.clone());
        }
        let work = Work::Closure {
            file: self.file,
            syntax: id,
            captures: capture,
            types: self.types.clone(),
            statics,
            tail_resume_k,
        };
        let function = self.global.queue(work);
        let arity = match &self.ast().expr(id).value {
            Expr::Closure { params, .. } => params.iter().filter(|param| !param.is_meta).count(),
            Expr::Accessor(_) => 1,
            _ => 0,
        };
        Ok(self.box_closure(function, arity, environment))
    }
}
