//! Explicit instantiation is an operation on a callable value. Static choices
//! survive ordinary value transport and are read from the actual call target.
use super::*;
use crate::sema::{
    copy_contract::CopyCallEventId,
    evaluated::{CapturedSource, SourceRef},
    model::GenericSelection,
    source_types::{SourceTypesError, TypeSourceSelection},
};
use std::sync::Arc;

impl Checker {
    pub(super) fn instantiate_named_value(
        &mut self,
        syntax: &Expr,
        packet: &mut EvaluatedValue,
    ) -> bool {
        let [Callable::Named(index, previous)] = packet.value.callables.as_slice() else {
            return false;
        };
        let index = *index;
        let base = packet.value.callables[0].clone();
        let info = self.functions[index].clone();
        if info.syntax.body.is_none() {
            return false;
        }
        let ExprKind::Generic { arguments, .. } = &syntax.kind else {
            return false;
        };
        let mut selections = previous
            .as_ref()
            .map_or_else(Vec::new, |v| v.selections.clone());
        let start = selections.len();
        let exposed = packet
            .value
            .signature
            .as_ref()
            .map_or(0, |signature| signature.generics.len());
        if arguments.is_empty()
            || arguments.len() > exposed
            || start + arguments.len() > info.syntax.generics.len()
        {
            self.error(
                "E0340",
                syntax.span,
                "generic argument list does not fit the callable declaration",
                [packet.value.cause],
            );
            packet.source_valid = false;
            return true;
        }
        let mut lease = self.application_effect.lease_work(131072);
        let mut stage = "callable type";
        let result = (|| {
            let work = lease.work();
            let (header, environment) = self
                .owned_result_type(packet, work)?
                .ok_or(SourceTypesError::Unresolved)?;
            for (offset, argument) in arguments.iter().enumerate() {
                stage = "type argument";
                let ordinal = start + offset;
                let parameter = &info.syntax.generics[ordinal];
                if packet
                    .value
                    .signature
                    .as_ref()
                    .and_then(|s| s.generics.get(offset))
                    .copied()
                    != parameter.hir_id
                {
                    return Err(SourceTypesError::Unresolved);
                }
                let mut binders = self
                    .generic_binders
                    .values()
                    .filter(|b| b.definition == info.definition && b.index as usize == ordinal);
                let binder = binders
                    .next()
                    .filter(|_| binders.next().is_none())
                    .ok_or(SourceTypesError::Unresolved)?;
                if !crate::sema::record_bounds::certifies_type_sort(
                    &binder.identity,
                    binder,
                    parameter,
                    &self.record_bounds,
                ) {
                    return Err(SourceTypesError::Unresolved);
                }
                let identity = binder.identity.clone();
                let ty = self.ty(argument);
                let ty = self.call_inference_type(&ty);
                let schema = self.original_header_source_schema(argument, work)?;
                stage = "argument selection";
                let (schema, context) =
                    self.selected_input_schema(schema, self.capture_typing_environment(), work)?;
                let frozen = self
                    .effect_argument_syntax(argument)
                    .map_err(|_| SourceTypesError::Unresolved)?;
                let key = crate::static_eval::effects::bounded_argument_key(
                    &frozen,
                    &self.effect_type_binders,
                )
                .ok_or(SourceTypesError::BudgetExceeded)?;
                let source =
                    TypeSourceSelection::from_elaborated(schema, frozen.clone(), context, work)?;
                selections.push(GenericSelection {
                    binder: identity,
                    index: ordinal as u32,
                    ty,
                    key,
                    source,
                });
            }
            stage = "lexical interpretation";
            let mut scope = packet
                .value
                .signature
                .as_ref()
                .map(|signature| signature.environment.clone())
                .or(header.callable_interpretation(work)?)
                .unwrap_or(environment)
                .thaw();
            for selected in &selections {
                scope
                    .generic_substitutions
                    .insert(selected.binder.clone(), selected.ty.clone());
                scope
                    .generic_sources
                    .insert(selected.binder.clone(), selected.source.clone());
            }
            let context = scope.freeze();
            let signature_context = context.clone();
            let (selected, context) = self.selected_input_schema(header, context, work)?;
            let selected = selected.capture_interpretation(&signature_context, true, work)?;
            SourceRef::intern(
                &selected,
                context,
                self.type_source.storage.live_types_mut(),
                work,
            )
            .map(|source| (source, signature_context))
        })();
        let returned = self.application_effect.return_work(lease);
        match result.and_then(|source| returned.map(|()| source)) {
            Ok((source, signature_context)) => {
                let types = selections
                    .iter()
                    .map(|s| (s.binder.clone(), s.ty.clone()))
                    .collect();
                packet.value.ty = super::types::substitute_inferred_type(&packet.value.ty, &types);
                packet.value.source_type_witness = None;
                if let Some(signature) = &packet.value.signature {
                    packet.value.signature = Some(Arc::new(CallableSignature {
                        parameters: signature.parameters.clone(),
                        environment: signature_context,
                        generics: signature
                            .generics
                            .iter()
                            .skip(arguments.len())
                            .copied()
                            .collect(),
                    }));
                }
                packet.value.callables = vec![Callable::Named(
                    index,
                    Some(Arc::new(NamedInstance {
                        target: info.definition,
                        selections,
                    })),
                )];
                if let Err(error) = packet.set_current_type(CapturedSource::Known(source)) {
                    packet.fail_current_source(error);
                } else if let Some(source) = syntax.hir_id
                    && let Some(activation) = self.application_effect.current_activation()
                {
                    let context =
                        self.application_effect.activations[activation.0 as usize].context;
                    self.callable_instantiations
                        .push(crate::sema::CallableInstantiation {
                            source,
                            context,
                            base,
                            result: packet.value.callables[0].clone(),
                        });
                } else {
                    self.unsupported(
                        syntax.span,
                        "callable instantiation has no resolved operation identity",
                    );
                }
            }
            Err(error) => {
                self.unsupported(
                    syntax.span,
                    format!("callable instantiation at {stage} is incomplete: {error}"),
                );
                packet.fail_current_source(error);
            }
        }
        true
    }

    pub(super) fn named_instance_for_event(
        &self,
        event: CopyCallEventId,
        target: DefinitionId,
    ) -> Option<Arc<NamedInstance>> {
        let call = self.copy_call_events.get(event.0 as usize)?;
        let value = &self
            .application_effect
            .expressions
            .get(call.callee_expression?)?
            .value;
        let [Callable::Named(index, instance)] = value.callables.as_slice() else {
            return None;
        };
        (self.functions[*index].definition == target)
            .then(|| instance.clone())
            .flatten()
    }

    pub(super) fn named_instance_for_invocation(
        &self,
        info: &FunctionInfo,
    ) -> Option<Arc<NamedInstance>> {
        let invocation = self
            .copy_invocations
            .get(self.copy_invocation_stack.last()?.0 as usize)?;
        (invocation.target == info.definition)
            .then(|| invocation.instance.clone())
            .flatten()
    }

    pub(super) fn seed_named_instance(&mut self, instance: &NamedInstance) {
        for selected in &instance.selections {
            self.type_source
                .environment
                .generic_substitutions
                .insert(selected.binder.clone(), selected.ty.clone());
            self.type_source
                .environment
                .generic_sources
                .insert(selected.binder.clone(), selected.source.clone());
        }
    }

    pub(super) fn finish_named_instance_inference(&mut self, instance: &NamedInstance, span: Span) {
        for selected in &instance.selections {
            if self
                .type_source
                .environment
                .generic_substitutions
                .get(&selected.binder)
                != Some(&selected.ty)
            {
                self.error(
                    "E0301",
                    span,
                    "actual input conflicts with the explicit complete type argument",
                    [],
                );
            }
        }
        self.seed_named_instance(instance);
    }

    pub(super) fn explicit_numeric_input(
        &self,
        event: CopyCallEventId,
        info: &FunctionInfo,
        binder: &str,
        expected: &Ty,
        arguments: &[crate::sema::effect_identity::StaticArgumentWitness],
    ) -> bool {
        let Some(current) = self
            .copy_invocation_stack
            .last()
            .and_then(|id| self.copy_invocations.get(id.0 as usize))
            .filter(|call| call.source_event == Some(event) && call.target == info.definition)
        else {
            return false;
        };
        if arguments.len() != info.syntax.generics.len() {
            return false;
        }
        current.instance.as_ref().is_some_and(|instance| {
            instance.selections.iter().any(|selection| {
                selection.binder == binder
                    && &selection.ty == expected
                    && self
                        .type_source
                        .environment
                        .generic_substitutions
                        .get(binder)
                        == Some(expected)
                    && arguments
                        .get(selection.index as usize)
                        .is_some_and(|argument| {
                            argument.binder == selection.binder
                                && argument.key.as_ref() == Some(&selection.key)
                        })
            })
        })
    }
}
