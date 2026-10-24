//! Numeric context is prepared in the callee's lexical binder environment.
//! Written argument evaluation stays in the caller and occurs exactly once.
use super::super::copy_contract::CopyCallEventId;
use super::super::numeric_selection::{ApplicationPhase, NumericPreparedApplication};
use super::*;
use crate::hir::application::Operand;
use crate::numeric_literals::{ExactLiteral, NumberType, ParseLimit};

struct NumericInputSnapshot {
    substitutions: BTreeMap<String, Ty>,
    parameter_templates: Vec<Option<Ty>>,
    binders: BTreeSet<String>,
}

fn numeric_input_snapshot(
    application: &NumericPreparedApplication,
    work: &mut usize,
) -> Result<NumericInputSnapshot, crate::sema::source_types::SourceTypesError> {
    use crate::sema::source_types::SourceTypesError;
    *work = work
        .checked_sub(
            application.substitutions.len()
                + application.parameter_templates.len()
                + application.binders.len()
                + 1,
        )
        .ok_or(SourceTypesError::BudgetExceeded)?;
    for (name, ty) in &application.substitutions {
        *work = work
            .checked_sub(1 + name.len().div_ceil(32))
            .ok_or(SourceTypesError::BudgetExceeded)?;
        crate::sema::clone_work::ty(work, ty, 0).ok_or(SourceTypesError::BudgetExceeded)?;
    }
    for ty in application.parameter_templates.iter().flatten() {
        crate::sema::clone_work::ty(work, ty, 0).ok_or(SourceTypesError::BudgetExceeded)?;
    }
    for name in &application.binders {
        *work = work
            .checked_sub(1 + name.len().div_ceil(32))
            .ok_or(SourceTypesError::BudgetExceeded)?;
    }
    Ok(NumericInputSnapshot {
        substitutions: application.substitutions.clone(),
        parameter_templates: application.parameter_templates.clone(),
        binders: application.binders.clone(),
    })
}

pub(super) struct PrimitiveNumericPrefix<'a> {
    pub event: CopyCallEventId,
    pub preparation: usize,
    pub packets: &'a [super::applications::EvaluatedOperand],
}

pub(super) struct NumericInputContext<'a> {
    pub event: CopyCallEventId,
    pub expected_result: Option<&'a Ty>,
    pub span: Span,
    /// Present only when every operand was already evaluated. Never consult
    /// the current lexical binding values to reinterpret these earlier inputs.
    pub frozen: Option<&'a [(ParameterMode, Value, Span)]>,
}

pub(super) fn selected_type(ty: NumberType) -> Ty {
    crate::sema::numeric_selection::selected_ty(ty)
}

impl Checker {
    pub(super) fn primitive_numeric_contexts(
        &mut self,
        id: ril_compiler_core::builtin_calls::GenericBuiltin,
        arguments: &[Operand<'_, &Expr>],
        mapping: &[Result<usize, &'static str>],
        prefix: PrimitiveNumericPrefix<'_>,
        frame: &Frame,
    ) -> Vec<Option<Ty>> {
        let PrimitiveNumericPrefix {
            event,
            preparation,
            packets: prefixes,
        } = prefix;
        if !self
            .application_effect
            .admit(prefixes.len() + arguments.len() + mapping.len())
        {
            self.unsupported(
                arguments.first().map_or(
                    Span {
                        file: self.file,
                        start: 0,
                        end: 0,
                    },
                    |arg| arg.span,
                ),
                "numeric prefix packet lookup exhausted its work bound",
            );
            return vec![None; mapping.len()];
        }
        let storage = &self.type_source.storage;
        let preparations = &self.call_arguments;
        let parameters = self.application_effect.with_work(|remaining| {
            let mut work = crate::sema::source_types::WorkLimit::new(*remaining);
            let answer = (|| {
                let receiver = arguments
                    .iter()
                    .zip(mapping)
                    .find(|(_, slot)| **slot == Ok(0))
                    .map(|(argument, _)| {
                        match prefixes.iter().find(|input| input.role == argument.role) {
                            Some(input) => {
                                let original = preparations
                                    .get(preparation)
                                    .filter(|row| row.source_event == event)
                                    .is_some_and(|row| {
                                        row.evaluated.iter().any(|child| {
                                            child.role == input.role
                                                && Some(child.observation.expression)
                                                    == input.value.observation
                                                && child.observation.allocation_epoch
                                                    == input.value.allocation_epoch
                                        })
                                    });
                                if original {
                                    input
                                        .value
                                        .birth_source(
                                            crate::sema::source_types_ref::SourceTypesRef::Live(
                                                storage.live_types(),
                                            ),
                                            &mut work,
                                        )
                                        .map(|source| source.into_known())
                                } else {
                                    Err(crate::sema::source_types::SourceTypesError::MissingNode)
                                }
                            }
                            None => storage.declared_operand_source_schema(
                                argument.expression,
                                &frame.env,
                                &mut work,
                            ),
                        }
                    });
                let receiver = receiver.transpose()?.flatten();
                crate::sema::source_types::polymorphic::numeric_parameters_schema(
                    id,
                    receiver.as_ref().map(|(schema, _)| schema),
                    &mut work,
                )
            })();
            *remaining = work.remaining();
            answer
        });
        let parameters = match parameters {
            Ok(parameters) => Some(parameters),
            Err(error) => {
                self.unsupported(
                    arguments.first().map_or(
                        Span {
                            file: self.file,
                            start: 0,
                            end: 0,
                        },
                        |argument| argument.span,
                    ),
                    format!("numeric input Source graph failed: {error}"),
                );
                None
            }
        };
        mapping
            .iter()
            .map(|slot| {
                let kind = parameters.as_ref()?.get(*slot.as_ref().ok()?)?.as_ref()?;
                let name = crate::sema::source_types::scalar_name(*kind).to_owned();
                Some(
                    if matches!(
                        kind,
                        crate::sema::source_types::SourceScalar::F32
                            | crate::sema::source_types::SourceScalar::F64
                    ) {
                        Ty::Float(name)
                    } else {
                        Ty::Int(name)
                    },
                )
            })
            .collect()
    }
    pub(super) fn numeric_argument_contexts(
        &mut self,
        callee: &Value,
        arguments: &[Operand<'_, &Expr>],
        context: NumericInputContext<'_>,
        frame: &Frame,
    ) -> Vec<Option<Ty>> {
        let NumericInputContext {
            event: source_event,
            expected_result,
            span,
            frozen,
        } = context;
        if arguments.len() == 1
            && let [Callable::Builtin(name)] = callee.callables.as_slice()
        {
            use ril_compiler_core::builtin_calls::PayloadConstructor;
            let payload = match (PayloadConstructor::lookup(name), expected_result) {
                (Some(PayloadConstructor::Some), Some(Ty::Optional(payload))) => Some(&**payload),
                (Some(PayloadConstructor::Ok), Some(Ty::Result(ok, _))) => Some(&**ok),
                (Some(PayloadConstructor::Err), Some(Ty::Result(_, error))) => Some(&**error),
                _ => None,
            };
            if let Some(payload) = payload {
                return vec![Some(payload.clone())];
            }
        }
        let [Callable::Named(id)] = callee.callables.as_slice() else {
            let Ty::Callable(parameters, _) = self.expanded_at(&callee.ty, span.file) else {
                return vec![None; arguments.len()];
            };
            let labels = callee
                .signature
                .as_ref()
                .map(|signature| crate::hir::application::parameter_labels(&signature.parameters))
                .unwrap_or_else(|| vec![None; parameters.len()]);
            return crate::hir::application::bind_slots(
                &labels,
                arguments.iter().map(|argument| argument.label),
            )
            .into_iter()
            .map(|slot| {
                let slot = slot.ok()?;
                let ty = parameters.get(slot)?.clone();
                let mut generics = BTreeSet::new();
                ty.generic_names(&mut generics);
                (generics.is_empty() && ty != Ty::Unknown).then_some(ty)
            })
            .collect();
        };
        let info = self.functions[*id].clone();
        let previous_typing = self.generic_scope(*id);
        let binders: BTreeSet<_> = info
            .syntax
            .generics
            .iter()
            .filter_map(|parameter| {
                self.type_source
                    .environment
                    .generic_context
                    .get(&parameter.name)
                    .cloned()
            })
            .collect();
        for binder in &binders {
            self.type_source
                .environment
                .generic_substitutions
                .remove(binder);
            self.type_source.environment.generic_sources.remove(binder);
            self.type_source
                .environment
                .static_key_arguments
                .remove(binder);
        }
        let templates: Vec<_> = info
            .syntax
            .parameters
            .iter()
            .map(|parameter| {
                parameter.ty.as_ref().map(|syntax| {
                    let ty = self.ty(syntax);
                    self.call_inference_type(&ty)
                })
            })
            .collect();
        let explicit = self.explicit_named_for_event(source_event, info.definition);
        let mut selected: BTreeMap<_, _> = explicit
            .iter()
            .flat_map(|prepared| prepared.selections.iter())
            .map(|selection| (selection.binder.clone(), selection.ty.clone()))
            .collect();
        if let Ty::Callable(parameters, _) = self.expanded_at(&callee.ty, span.file) {
            for (template, actual) in templates.iter().zip(&parameters) {
                if let Some(template) = template
                    && super::numeric::numeric_type(actual).is_some()
                    && (matches!(template,Ty::Generic(identity) if binders.contains(identity))
                        || super::numeric::numeric_type(template).is_some())
                    && !super::types::unify_call_types(template, actual, &binders, &mut selected)
                {
                    self.error(
                        "E0301",
                        span,
                        "callable interface conflicts with its numeric instance",
                        [callee.cause],
                    );
                }
            }
        }
        if let Some(expected) =
            expected_result.filter(|ty| super::numeric::numeric_type(ty).is_some())
            && let Some(result) = &info.syntax.return_type
        {
            let result = self.ty(result);
            let result = self.call_inference_type(&result);
            if (matches!(&result,Ty::Generic(identity) if binders.contains(identity))
                || super::numeric::numeric_type(&result).is_some())
                && !super::types::unify_call_types(&result, expected, &binders, &mut selected)
            {
                self.error(
                    "E0301",
                    span,
                    "call result does not fit its receiving numeric type",
                    [callee.cause],
                );
            }
        }
        // An expected-only binder needs explicit instance witness transport;
        // do not let the older late-result inference invent that proof.
        let mut input_binders = BTreeSet::new();
        for template in templates.iter().flatten() {
            template.generic_names(&mut input_binders);
        }
        // This is a deferred candidate only. No actual source has been
        // evaluated or checked yet. validate_numeric_application must consume
        // this exact invocation's completed structural input equation before
        // freezing any selection absent from the ordinary input templates.
        let deferred = self.potential_bound_numeric_inputs(&info, &templates);
        let explicit_binders: BTreeSet<_> = explicit
            .iter()
            .flat_map(|prepared| {
                prepared
                    .selections
                    .iter()
                    .map(|selection| selection.binder.clone())
            })
            .collect();
        if selected.keys().any(|binder| {
            !input_binders.contains(binder)
                && !deferred.contains(binder)
                && !explicit_binders.contains(binder)
        }) {
            self.unsupported(span,"expected-only generic numeric selection requires an explicit prepared instance witness");
        }
        self.restore_typing_environment(previous_typing);

        let interface = callee
            .signature
            .as_ref()
            .map(|signature| &signature.parameters)
            .unwrap_or(&info.syntax.parameters);
        let labels = crate::hir::application::parameter_labels(interface);
        let slots: Vec<_> = crate::hir::application::bind_slots(
            &labels,
            arguments.iter().map(|argument| argument.label),
        )
        .into_iter()
        .map(Result::ok)
        .collect();
        for (index, (argument, slot)) in arguments.iter().zip(&slots).enumerate() {
            let Some(template) = slot.and_then(|slot| templates[slot].as_ref()) else {
                continue;
            };
            let actual = match frozen {
                Some(values) => values.get(index).and_then(|(_, value, _)| {
                    (!value.unsuffixed_numeric && super::numeric::numeric_type(&value.ty).is_some())
                        .then(|| value.ty.clone())
                }),
                None => self.rigid_numeric_argument(argument.expression, frame),
            };
            let Some(actual) = actual else {
                continue;
            };
            let mut mentioned = BTreeSet::new();
            template.generic_names(&mut mentioned);
            if !mentioned.is_disjoint(&binders)
                && !super::types::unify_call_types(template, &actual, &binders, &mut selected)
            {
                self.error(
                    "E0301",
                    argument.span,
                    "written argument types require inconsistent generic instances",
                    [callee.cause],
                );
            }
        }
        let contexts: Vec<_> = slots
            .into_iter()
            .map(|slot| {
                let slot = slot?;
                let template = templates[slot].as_ref()?;
                let ty = super::types::substitute_inferred_type(template, &selected);
                let mut unresolved = BTreeSet::new();
                ty.generic_names(&mut unresolved);
                // Row/static-key projections need their existing full input
                // inference before their result is known. Only a direct
                // unsolved scalar binder enters this numeric-hole protocol.
                (unresolved.is_disjoint(&binders) || !matches!(ty, Ty::Generic(_))).then_some(ty)
            })
            .collect();
        if !binders.is_empty()
            || !selected.is_empty()
            || frozen.is_some_and(|values| {
                values
                    .iter()
                    .any(|(_, value, _)| matches!(value.ty, Ty::NumericHole(_)))
            })
        {
            self.numeric.applications.insert(
                source_event,
                NumericPreparedApplication {
                    event: source_event,
                    span,
                    target: Some(info.definition),
                    context: self.invocation_context(frame.callable_owner),
                    expected_result: expected_result.cloned(),
                    arguments: Vec::new(),
                    substitutions: selected,
                    parameter_templates: templates,
                    binders,
                    static_arguments: Vec::new(),
                    phase: ApplicationPhase::Collecting,
                },
            );
        }
        contexts
    }

    pub(super) fn rigid_numeric_argument(&self, expression: &Expr, frame: &Frame) -> Option<Ty> {
        // Reading a stored type or a written suffix does not evaluate a value.
        // Unsuffixed literals and arbitrary expressions remain unresolved;
        // neither their default type nor a speculative result is evidence.
        if let ExprKind::Name(name) = &expression.kind {
            let value = &self.bindings[*frame.env.get(name)?].value;
            return (!value.unsuffixed_numeric
                && super::numeric::numeric_type(&value.ty).is_some())
            .then(|| value.ty.clone());
        }
        if let ExprKind::Binary { left, right, .. } = &expression.kind
            && super::numeric_pending::candidate(expression)
        {
            return self
                .rigid_numeric_argument(left, frame)
                .or_else(|| self.rigid_numeric_argument(right, frame));
        }
        if let ExprKind::Call { callee, .. } = &expression.kind
            && let ExprKind::Name(name) = &callee.kind
        {
            // A closed stored callable interface fixes its result regardless
            // of its effects. No argument or body is evaluated by this query.
            let value = &self.bindings[*frame.env.get(name)?].value;
            if let Ty::Callable(_, result) = &value.ty {
                return super::numeric::numeric_type(result).map(|_| (**result).clone());
            }
        }
        let (expression, minus) = match &expression.kind {
            ExprKind::Unary { operator, operand } if operator == "-" => (&**operand, true),
            _ => (expression, false),
        };
        let limit = ParseLimit {
            max_bytes: 1_048_576,
        };
        let exact = match &expression.kind {
            ExprKind::Literal(Literal::Integer(text)) => ExactLiteral::integer(text, minus, limit),
            ExprKind::Literal(Literal::Float(text)) => {
                if let Ok(Some(committed)) = crate::static_eval::committed_float::decode(text) {
                    return Some(Ty::Float(format!("f{}", committed.width)));
                }
                ExactLiteral::decimal(text, minus, limit)
            }
            _ => return None,
        }
        .ok()?;
        exact.written_type().map(selected_type)
    }

    pub(super) fn finish_numeric_arguments(
        &mut self,
        event: CopyCallEventId,
        args: &mut [(ParameterMode, Value, Span)],
    ) -> Result<(), crate::sema::source_types::SourceTypesError> {
        if args.iter().any(|(_, value, _)| value.ty == Ty::Never) {
            for (_, value, _) in args.iter_mut() {
                if let Ty::NumericHole(id) = value.ty {
                    let expected = self
                        .numeric_preference(id)?
                        .unwrap_or_else(|| Ty::Int("int".into()));
                    self.commit_numeric_value(value, &expected)?;
                }
            }
            // No body enters; every currently supported literal context is
            // already committed and grants no late substitution authority.
            self.numeric.applications.remove(&event);
        } else if let Some(application) = self.numeric.applications.get_mut(&event) {
            application.arguments = args
                .iter()
                .map(|(_, value, _)| value.numeric.clone())
                .collect();
            application.phase = ApplicationPhase::Solved;
        }
        Ok(())
    }

    pub(super) fn solve_numeric_slots(
        &mut self,
        event: CopyCallEventId,
        slots: &mut [Option<(ParameterMode, EvaluatedValue, Span)>],
    ) -> Result<(), crate::sema::source_types::SourceTypesError> {
        use crate::sema::source_types::SourceTypesError;
        if !self.numeric.applications.contains_key(&event) {
            return Ok(());
        }
        if !self.application_effect.admit(slots.len().saturating_mul(2)) {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let actual: Vec<_> = slots
            .iter()
            .map(|slot| {
                slot.as_ref()
                    .map(|(_, value, span)| Ok((self.read_evaluation_packet(value, *span)?, *span)))
                    .transpose()
            })
            .collect::<Result<_, SourceTypesError>>()?;
        if !actual
            .iter()
            .flatten()
            .any(|(value, _)| matches!(value.ty, Ty::NumericHole(_)))
        {
            return Ok(());
        }
        let application = self
            .numeric
            .applications
            .get(&event)
            .ok_or(SourceTypesError::MissingNode)?;
        let application = self
            .application_effect
            .with_work(|work| numeric_input_snapshot(application, work))?;
        let roots: Vec<_> = actual
            .iter()
            .flatten()
            .filter_map(|(value, _)| match value.ty {
                Ty::NumericHole(id) => Some(id),
                _ => None,
            })
            .collect();
        let preferences = self.numeric_preferences(&roots)?;
        let mut selected = application.substitutions;
        for (actual, template) in actual.iter().zip(&application.parameter_templates) {
            let (Some((value, span)), Some(template)) = (actual, template) else {
                continue;
            };
            if matches!(value.ty, Ty::NumericHole(_)) {
                continue;
            }
            if value.unsuffixed_numeric {
                self.unsupported(*span,"a previously evaluated nonliteral numeric expression needs a deferred term certificate");
                continue;
            }
            let ty = self.collection_type(value);
            if !super::types::unify_call_types(template, &ty, &application.binders, &mut selected) {
                self.error(
                    "E0301",
                    *span,
                    "actual argument requires a conflicting generic instance",
                    [value.cause],
                );
            }
        }
        // Written types inside a pending tree and floating-only holes constrain
        // their binders before a remaining integer hole takes the int default.
        for defaults in [false, true] {
            for (actual, template) in actual.iter().zip(&application.parameter_templates) {
                let (Some((value, span)), Some(template)) = (actual, template) else {
                    continue;
                };
                let Ty::NumericHole(id) = value.ty else {
                    continue;
                };
                if super::numeric::numeric_type(&super::types::substitute_inferred_type(
                    template, &selected,
                ))
                .is_some()
                {
                    continue;
                }
                let preferred = preferences.get(id, defaults)?;
                if let Some(preferred) = preferred
                    && !super::types::unify_call_types(
                        template,
                        &preferred,
                        &application.binders,
                        &mut selected,
                    )
                {
                    self.error(
                        "E0301",
                        *span,
                        "numeric operands require conflicting selected types",
                        [value.cause],
                    );
                }
            }
        }
        for (index, slot) in slots.iter_mut().enumerate() {
            let Some((_, value, span)) = slot else {
                continue;
            };
            if !matches!(value.value.ty, Ty::NumericHole(_)) {
                continue;
            }
            let Ty::NumericHole(id) = value.value.ty else {
                unreachable!()
            };
            let Some(template) = application
                .parameter_templates
                .get(index)
                .and_then(Option::as_ref)
            else {
                self.unsupported(
                    *span,
                    "pending numeric argument has no canonical parameter template",
                );
                continue;
            };
            let mut expected = super::types::substitute_inferred_type(template, &selected);
            let mut unresolved = BTreeSet::new();
            expected.generic_names(&mut unresolved);
            if !unresolved.is_disjoint(&application.binders) {
                expected = preferences
                    .get(id, true)?
                    .unwrap_or_else(|| Ty::Int("int".into()));
                if !super::types::unify_call_types(
                    template,
                    &expected,
                    &application.binders,
                    &mut selected,
                ) {
                    self.error(
                        "E0301",
                        *span,
                        "numeric default conflicts with a selected generic type",
                        [value.value.cause],
                    );
                }
            }
            self.select_numeric_packet(value, &expected, *span)?;
        }
        self.numeric
            .applications
            .get_mut(&event)
            .expect("prepared numeric application")
            .substitutions = selected;
        Ok(())
    }

    pub(super) fn validate_numeric_application(&mut self, info: &FunctionInfo, span: Span) {
        let Some(invocation) = self.copy_invocation_stack.last().copied() else {
            return;
        };
        let call = self.copy_invocations[invocation.0 as usize].clone();
        let Some(event) = call.source_event else {
            return;
        };
        let Some(application) = self.numeric.applications.get(&event).cloned() else {
            return;
        };
        let source = self.copy_call_events.get(event.0 as usize);
        if application.target != Some(info.definition)
            || application.event != event
            || application.span != span
            || call.target != info.definition
            || source.is_none_or(|source| {
                source.id != event
                    || source.target != Some(info.definition)
                    || source.owner != application.context.owner
                    || source.parent != application.context.invocation
            })
            || application.phase != ApplicationPhase::Solved
        {
            self.unsupported(
                span,
                "numeric application context does not match the actual generic instance",
            );
            if let Some(application) = self.numeric.applications.get_mut(&event) {
                application.phase = ApplicationPhase::Invalid;
            }
            return;
        }
        if application.substitutions.iter().any(|(binder, expected)| {
            self.type_source
                .environment
                .generic_substitutions
                .get(binder)
                != Some(expected)
        }) {
            let conflict = application.substitutions.iter().any(|(binder, expected)| {
                self.type_source
                    .environment
                    .generic_substitutions
                    .get(binder)
                    .is_some_and(|actual| {
                        actual != expected
                            && super::numeric::numeric_type(actual).is_some()
                            && super::numeric::numeric_type(expected).is_some()
                    })
            });
            if conflict {
                self.error(
                    "E0301",
                    span,
                    "prepared numeric result conflicts with its verified input type",
                    [],
                );
            } else {
                self.unsupported(
                    span,
                    "numeric application context does not match the actual generic instance",
                );
            }
            if let Some(application) = self.numeric.applications.get_mut(&event) {
                application.phase = ApplicationPhase::Invalid;
            }
            return;
        }
        let arguments = self.static_arguments_for(info, span).arguments;
        let mut inputs = BTreeSet::new();
        for template in application.parameter_templates.iter().flatten() {
            template.generic_names(&mut inputs);
        }
        let deferred = self.potential_bound_numeric_inputs(info, &application.parameter_templates);
        for (binder, expected) in application
            .substitutions
            .iter()
            .filter(|(binder, _)| !inputs.contains(*binder))
        {
            if self.explicit_numeric_input(event, info, binder, expected, &arguments) {
                continue;
            }
            let own = self
                .generic_binders
                .get(binder)
                .filter(|own| own.definition == info.definition);
            let actual = own.and_then(|own| {
                arguments.get(own.index as usize).filter(|actual| {
                    actual.definition == info.definition
                        && actual.index == own.index
                        && actual.binder == *binder
                })
            });
            if !deferred.contains(binder)
                || actual.is_none_or(|actual| actual.key.is_none() || actual.syntax.is_none())
                || !self.proved_bound_numeric_input(info, invocation, binder, expected)
            {
                self.unsupported(
                    span,
                    "deferred numeric selection lacks its actual complete structural input witness",
                );
                if let Some(application) = self.numeric.applications.get_mut(&event) {
                    application.phase = ApplicationPhase::Invalid;
                }
                return;
            }
        }
        let application = self
            .numeric
            .applications
            .get_mut(&event)
            .expect("prepared application");
        application.static_arguments = arguments;
        application.phase = ApplicationPhase::Frozen;
    }
}

#[cfg(test)]
mod snapshot_tests {
    use super::*;
    #[test]
    fn numeric_input_snapshots_admit_the_complete_selected_fields_before_copying() {
        let application = NumericPreparedApplication {
            event: CopyCallEventId(0),
            span: Span {
                file: FileId(0),
                start: 0,
                end: 0,
            },
            target: None,
            context: crate::sema::effect_identity::InvocationContext {
                invocation: None,
                owner: None,
                closure: None,
                closure_invocation: None,
                budget_validation: false,
                default_use: None,
            },
            expected_result: None,
            arguments: Vec::new(),
            substitutions: BTreeMap::from([(
                "T".into(),
                Ty::Tuple(vec![Ty::Float("f32".into()); 64]),
            )]),
            parameter_templates: vec![Some(Ty::Tuple(vec![Ty::Generic("T".into()); 64]))],
            binders: BTreeSet::from(["T".into()]),
            static_arguments: Vec::new(),
            phase: ApplicationPhase::Collecting,
        };
        for allowance in [0, 8, 64] {
            assert!(matches!(
                numeric_input_snapshot(&application, &mut { allowance }),
                Err(crate::sema::source_types::SourceTypesError::BudgetExceeded)
            ));
        }
        let snapshot = numeric_input_snapshot(&application, &mut 4096).unwrap();
        assert_eq!(snapshot.substitutions, application.substitutions);
        assert_eq!(
            snapshot.parameter_templates,
            application.parameter_templates
        );
        assert_eq!(snapshot.binders, application.binders);
    }
}
