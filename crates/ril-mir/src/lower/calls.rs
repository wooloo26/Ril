use std::collections::BTreeMap;

use ril_sema::{
    hir::{DefinitionId, DefinitionKind},
    syntax::{Argument, Expr, ExprId, Parameter},
    ty::{Ty, Value},
};
use ril_source::span::{FileId, Span};

use super::{Builder, Result, Work};
use crate::{Instruction, Register, Target};

impl Builder<'_, '_> {
    pub(super) fn call(
        &mut self,
        callee: ExprId,
        args: &[Argument],
        span: Span,
    ) -> Result<Register> {
        let callee_expression = &self.ast().expr(callee).value;
        let Expr::Path(path) = callee_expression else {
            if let Expr::Closure { params, .. } = callee_expression
                && params.iter().any(|param| param.is_meta)
            {
                let metadata =
                    self.global
                        .typed
                        .static_arguments(span, &self.statics, &self.types)?;
                let value = self.lift(callee, Some(&metadata))?;
                let args = self.arguments(params, self.file, args, &metadata, span)?;
                return Ok(self.invoke_closure(value, args));
            }
            let callee_span = self.ast().expr(callee).span;
            let value = self.expr(callee)?;
            let args = self.indirect_arguments(callee_span, args, span)?;
            return Ok(self.invoke_closure(value, args));
        };
        let id = self
            .global
            .resolve(path.span)
            .ok_or_else(|| self.unsupported(span, "unresolved call"))?;
        let def = self.global.typed.hir.definition(id);
        let name = def.name.value.as_str();
        if matches!(def.kind, DefinitionKind::Primitive(_)) {
            if let Some(module @ ("Fiber" | "Channel")) = self.global.typed.hir.primitive_module(id)
            {
                return self.concurrent(module, name, args, span);
            }
            return self.primitive(id, name, args, span);
        }
        if let Some(label) = self
            .global
            .typed
            .operation_evidence(id, path.span, &self.types)
        {
            let operation = self
                .global
                .declaration(id)
                .ok_or_else(|| self.unsupported(span, "missing effect operation"))?;
            let args = self.arguments(
                &operation.signature.params,
                operation.name.span.file,
                args,
                &BTreeMap::new(),
                span,
            )?;
            let op_id = self.global.effect_op_id(&label);
            let key = self.instruction(Instruction::RawU64(op_id));
            let handler = self.runtime("ril_rt_evidence_find", vec![self.evidence, key]);
            return Ok(self.invoke_closure(handler, args));
        }
        if def.kind == DefinitionKind::Local {
            let callee_span = self.ast().expr(callee).span;
            let closure = self.read(id, span)?;
            let args = self.indirect_arguments(callee_span, args, span)?;
            return Ok(self.invoke_closure(closure, args));
        }
        if matches!(def.kind, DefinitionKind::Variant(_) | DefinitionKind::Type) {
            let unit_payload = args.is_empty() && matches!(def.kind, DefinitionKind::Variant(_));
            let mut args = args
                .iter()
                .map(|arg| self.expr(arg.value))
                .collect::<Result<Vec<_>>>()?;
            if unit_payload {
                args.push(self.unit());
            }
            if let Some(&arity) = self.global.typed.tuple_payloads.get(&span)
                && let [tuple] = args.as_slice()
            {
                let tuple = *tuple;
                args = (0..arity)
                    .map(|index| {
                        let index = self.integer(&index.to_string());
                        self.runtime("ril_rt_load", vec![tuple, index])
                    })
                    .collect();
            }
            return Ok(self.tag(name, args));
        }
        let Some(function) = self.global.declaration(id) else {
            return Err(self.unsupported(span, "callable value"));
        };
        let metadata = self
            .global
            .typed
            .static_arguments(span, &self.statics, &self.types)?;
        let values = self.arguments(
            &function.signature.params,
            function.name.span.file,
            args,
            &metadata,
            span,
        )?;
        if function.body.is_some() {
            let (types, statics) = self.project_callee_env(id, span, metadata);
            let captures = self.named_captures(id);
            let environment = (!captures.is_empty()).then(|| self.environment(&captures));
            let function = self.global.queue(Work::Named(id, types, captures, statics));
            let target = environment.map_or(Target::Function(function), |environment| {
                Target::FunctionWithEnv {
                    function,
                    environment,
                }
            });
            Ok(self.invoke(target, values, false))
        } else {
            Ok(self.invoke(Target::Foreign(self.global.foreign(id)?), values, false))
        }
    }

    pub(super) fn project_callee_env(
        &self,
        id: DefinitionId,
        call_span: Span,
        extra_statics: BTreeMap<DefinitionId, Value>,
    ) -> (BTreeMap<DefinitionId, Ty>, BTreeMap<DefinitionId, Value>) {
        // Top-level and `sub`-level functions have no enclosing function scope, so
        // they depend solely on their own generic and meta arguments — never the
        // caller's unrelated `self.types`/`self.statics`. Local functions and `where`
        // helpers retain enclosing bindings.
        let is_top_level = self.global.top_level_fns.contains(&id);
        let mut types = if is_top_level {
            BTreeMap::new()
        } else {
            self.types.clone()
        };
        if let Some(arguments) = self.global.typed.type_arguments.get(&call_span) {
            types.extend(
                arguments
                    .iter()
                    .map(|(&param, ty)| (param, self.concrete(ty))),
            );
        }
        let mut statics = if is_top_level {
            BTreeMap::new()
        } else {
            self.statics.clone()
        };
        statics.extend(extra_statics);
        (types, statics)
    }

    pub(super) fn concrete(&self, ty: &Ty) -> Ty {
        ty.specialize(&self.types)
    }

    pub(super) fn arguments(
        &mut self,
        parameters: &[Parameter],
        callee_file: FileId,
        args: &[Argument],
        metadata: &BTreeMap<DefinitionId, Value>,
        span: Span,
    ) -> Result<Vec<Register>> {
        let mut values = vec![None; parameters.len()];
        let mut provided = vec![false; values.len()];
        for arg in args {
            let index = if let Some(name) = &arg.name {
                parameters.iter().position(|p| {
                    p.name
                        .as_ref()
                        .is_some_and(|param| param.value == name.value)
                })
            } else {
                provided.iter().position(|present| !present)
            }
            .ok_or_else(|| self.unsupported(span, "argument binding"))?;
            if let Some(provided) = provided.get_mut(index) {
                *provided = true;
            }
            if parameters.get(index).is_some_and(|param| !param.is_meta) {
                let value = self.expr(arg.value)?;
                if let Some(slot) = values.get_mut(index) {
                    *slot = Some(value);
                }
            }
        }
        let file = self.file;
        let locals = self.locals.clone();
        let statics = self.statics.clone();
        self.statics.extend(metadata.clone());
        self.file = callee_file;
        let mut ordered = Vec::new();
        let result = (|| {
            for (param, value) in parameters.iter().zip(values) {
                if param.is_meta {
                    continue;
                }
                let value = if let Some(value) = value {
                    value
                } else if let Some(default) = param.default {
                    self.expr(default)?
                } else {
                    return Err(self.unsupported(span, "missing argument"));
                };
                if let Some(id) = param
                    .name
                    .as_ref()
                    .and_then(|name| self.global.resolve(name.span))
                {
                    self.locals.insert(id, value);
                }
                ordered.push(value);
            }
            Ok(ordered)
        })();
        self.file = file;
        self.locals = locals;
        self.statics = statics;
        result
    }

    fn indirect_arguments(
        &mut self,
        callee_span: Span,
        args: &[Argument],
        span: Span,
    ) -> Result<Vec<Register>> {
        if !args.iter().any(|arg| arg.name.is_some()) {
            return args.iter().map(|arg| self.expr(arg.value)).collect();
        }
        let Some(Ty::Callable(sig)) = self.global.typed.types.get(&callee_span) else {
            return args.iter().map(|arg| self.expr(arg.value)).collect();
        };
        let mut provided = vec![false; sig.parameters.len()];
        let mut values = vec![None; sig.parameters.len()];
        for arg in args {
            let index = if let Some(name) = &arg.name {
                sig.parameters
                    .iter()
                    .position(|p| p.label.as_deref() == Some(name.value.as_str()))
            } else {
                provided.iter().position(|present| !present)
            }
            .ok_or_else(|| self.unsupported(span, "indirect argument binding"))?;
            if let Some(present) = provided.get_mut(index) {
                *present = true;
            }
            let value = self.expr(arg.value)?;
            if let Some(slot) = values.get_mut(index) {
                *slot = Some(value);
            }
        }
        values
            .into_iter()
            .map(|slot| slot.ok_or_else(|| self.unsupported(span, "missing indirect argument")))
            .collect()
    }
}
