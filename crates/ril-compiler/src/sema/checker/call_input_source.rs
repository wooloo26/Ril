//! Original input schemas, before any receiving ascription. Stored array
//! cardinality is deliberately absent; only a real literal AST supplies fresh
//! receiving context. This private state is replayed through CallArguments.
use super::*;
use crate::hir::application::EvaluationRole;
use crate::sema::{
    context::FrozenEnvironment,
    copy_contract::CopyCallEventId,
    default_uses::DefaultUseId,
    effect_identity::{ArgumentKey, InvocationContext},
    evaluated::{CapturedSource, SourceRef},
    source_reception::{self, Construction},
    source_types::{SourceSchema, SourceTypesError, WorkLimit},
    source_types_ref::SourceTypesRef,
};
#[path = "closure_parameter_sources.rs"]
mod closure_parameters;
#[path = "call_input_source_closures.rs"]
mod closure_sources;
#[path = "call_input_source_composites.rs"]
mod composites;
#[path = "constructor_input_source.rs"]
mod constructor_inputs;
#[path = "contextual_construction.rs"]
mod contextual_construction;
#[path = "call_input_source_graph.rs"]
mod graph_sources;
#[path = "call_input_source_headers.rs"]
mod headers;
#[path = "numeric_source_declarations.rs"]
mod numeric_sources;
#[path = "call_input_source_result.rs"]
mod producing_result;
#[path = "storage_input_source.rs"]
mod storage_inputs;

#[derive(Clone, Debug)]
struct Input {
    // Caller boundary context differs from a default's birth context.
    context: InvocationContext,
    packet: std::sync::Arc<EvaluatedValue>,
    default: Option<DefaultUseId>,
}
impl std::ops::Deref for Input {
    type Target = EvaluatedValue;
    fn deref(&self) -> &Self::Target {
        &self.packet
    }
}

#[derive(Default)]
pub(super) struct State {
    supplied: BTreeMap<CopyCallEventId, BTreeMap<usize, Input>>,
    defaults: BTreeMap<(CopyCallEventId, usize), Input>,
    operands: Vec<Operand>,
    carriers: BTreeMap<u32, (CopyCallEventId, InvocationContext)>,
    carrier_sources: BTreeMap<u32, SourceRef>,
    closure_views: BTreeMap<usize, (u32, SourceRef)>,
}

type InputSource = crate::sema::evaluated::CheckedSource;

struct Operand {
    source_id: Option<ril_compiler_core::ids::ExprId>,
    context: InvocationContext,
    event: CopyCallEventId,
    slot: u32,
}

impl Checker {
    pub(super) fn supplied_input_source(
        &self,
        event: CopyCallEventId,
        slot: usize,
        work: &mut WorkLimit,
    ) -> InputSource {
        work.charge(1)?;
        self.call_input_source
            .supplied
            .get(&event)
            .and_then(|inputs| inputs.get(&slot))
            .ok_or(SourceTypesError::MissingNode)?
            .input_source(
                SourceTypesRef::Live(self.type_source.storage.live_types()),
                work,
            )
            .map(|source| source.into_known())
    }
    pub(super) fn receive_application_source(
        &mut self,
        expected: &SourceSchema,
        event: CopyCallEventId,
        slot: usize,
        value: &Value,
        span: Span,
    ) -> bool {
        let input = self
            .call_input_source
            .supplied
            .get(&event)
            .and_then(|inputs| inputs.get(&slot))
            .cloned();
        let answer = input
            .as_ref()
            .ok_or(SourceTypesError::MissingNode)
            .and_then(|input| {
                input_compatible(
                    expected,
                    input,
                    SourceTypesRef::Live(self.type_source.storage.live_types()),
                    &mut WorkLimit::new(16384),
                )
            });
        match answer {
            Ok(true) => true,
            Ok(false) => {
                self.error(
                    "E0301",
                    span,
                    "actual input does not fit the declared complete Source view",
                    [value.cause],
                );
                false
            }
            Err(error) => {
                self.unsupported(
                    span,
                    format!(
                        "input reception lacks its original complete Source observation: {error}"
                    ),
                );
                false
            }
        }
    }
    pub(super) fn supplied_parameter_source(
        &mut self,
        slot: usize,
    ) -> Option<std::sync::Arc<crate::sema::source_types::TypeSourceSelection>> {
        use crate::sema::source_types::{SourceSelectionInput, TypeSourceSelection, WorkLimit};
        let invocation = *self.copy_invocation_stack.last()?;
        let call = self.copy_invocations.get(invocation.0 as usize)?;
        let event = call.source_event?;
        let input = self
            .call_input_source
            .supplied
            .get(&event)?
            .get(&slot)?
            .clone();
        let mut work = WorkLimit::new(16384);
        let (actual, actual_environment) = match input
            .input_source(
                SourceTypesRef::Live(self.type_source.storage.live_types()),
                &mut work,
            )
            .map(|source| source.into_known())
        {
            Ok(Some(source)) => source,
            Ok(None) => return None,
            Err(error) => {
                self.unsupported(
                    call.span,
                    format!("supplied parameter Source observation failed: {error}"),
                );
                return None;
            }
        };
        if actual_environment.is_poisoned() {
            self.unsupported(
                call.span,
                "supplied parameter Source has a poisoned environment",
            );
            return None;
        }
        let observation = input.observation?;
        let fact = self.application_effect.expressions.get(observation)?;
        if fact.value.sources.len() != 1 {
            return None;
        }
        let binding = *fact.value.sources.first()?;
        let info = self.bindings.get(binding)?;
        if !info.parameter {
            return None;
        }
        let node = self.semantic_hir.expression(fact.source_id?)?;
        if !matches!(&node.kind, crate::hir::nodes::ExprKind::Name(name) if name == &info.name) {
            return None;
        }
        let (syntax, environment) = self.formal_binding_declaration(binding, &info.name)?;
        let recorded = self.parameter_source_schema_if_known(binding, syntax.hir_id, &mut work);
        let (schema, original_environment) = match recorded {
            Ok(Some(source)) => source,
            Ok(None) => return None,
            Err(error) => {
                self.unsupported(
                    syntax.span,
                    format!("formal parameter Source graph failed: {error}"),
                );
                return None;
            }
        };
        let agrees = match schema.equivalent(&actual, &mut work) {
            Ok(answer) => answer,
            Err(error) => {
                self.unsupported(
                    syntax.span,
                    format!("supplied Source graph comparison failed: {error}"),
                );
                return None;
            }
        };
        if environment.id() != original_environment.id()
            || actual_environment.id() != original_environment.id()
            || !agrees
        {
            return None;
        }
        let source_span = syntax.span;
        match TypeSourceSelection::from_parameter(
            schema,
            syntax,
            environment,
            SourceSelectionInput {
                invocation,
                event,
                slot: u32::try_from(slot).ok()?,
                observation,
                binding,
            },
        ) {
            Ok(source) => Some(source),
            Err(error) => {
                self.unsupported(
                    source_span,
                    format!("parameter Source selection admission failed: {error}"),
                );
                None
            }
        }
    }
    pub(super) fn remember_constructor_carrier(
        &mut self,
        callee: &Value,
        value: &Value,
        event: Option<CopyCallEventId>,
        frame: &Frame,
    ) {
        if let Some(event) = event
            && matches!(callee.callables.as_slice(),[Callable::Builtin(name)] if ril_compiler_core::builtin_calls::PayloadConstructor::lookup(name).is_some())
        {
            self.call_input_source.carriers.insert(
                value.cause.0,
                (event, self.invocation_context(frame.callable_owner)),
            );
        }
    }
    pub(super) fn call_argument_source_contexts(
        &mut self,
        callee: &Value,
        event: CopyCallEventId,
    ) -> Vec<Option<source_reception::Target>> {
        let [Callable::Named(index)] = callee.callables.as_slice() else {
            return Vec::new();
        };
        let info = self.functions[*index].clone();
        let previous = self.generic_scope(*index);
        let owned: BTreeSet<_> = info
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
        for binder in &owned {
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
        if let Some(prepared) = self.explicit_named_for_event(event, info.definition) {
            self.seed_explicit_named(&prepared);
        }
        self.set_contract_environment(&info.lexical);
        // Operand contexts are prepared before the callee has a body entry.
        // Select its original static arguments at this application event;
        // the caller's top invocation is not the callee's interpretation.
        let span = self
            .copy_call_events
            .get(event.0 as usize)
            .map_or(info.syntax.span, |event| event.span);
        let selected = match self.actual_input_source_schemas(
            info.definition,
            Some(event),
            span,
            &mut WorkLimit::new(16384),
        ) {
            Ok(selected) => selected,
            Err(error) => {
                self.unsupported(
                    span,
                    format!("operand Source context lost its actual static selection: {error}"),
                );
                self.restore_typing_environment(previous);
                return Vec::new();
            }
        };
        let result = info
            .syntax
            .parameters
            .iter()
            .map(|parameter| {
                let syntax = parameter.ty.as_ref()?;
                let mut target = self.freeze_source_receiving_target(syntax);
                let schema = target.schema.as_ref()?;
                let mut work = WorkLimit::new(16384);
                let required = match schema.binder_identities(&mut work) {
                    Ok(required) => required,
                    Err(error) => {
                        self.unsupported(
                            syntax.span,
                            format!("operand Source context has unresolved coordinates: {error}"),
                        );
                        return None;
                    }
                };
                for identity in required.intersection(&owned) {
                    let source = selected.get(identity)?;
                    match source.bare_binder_identity(&mut work) {
                        Ok(Some(actual)) if actual == *identity => return None,
                        Ok(_) => {}
                        Err(error) => {
                            self.unsupported(
                                syntax.span,
                                format!(
                                    "operand Source context has an unresolved selection: {error}"
                                ),
                            );
                            return None;
                        }
                    }
                }
                match schema.substitute(&selected, &mut WorkLimit::new(16384)) {
                    Ok(schema) => target.schema = Some(schema),
                    Err(error) => {
                        self.unsupported(
                            syntax.span,
                            format!("operand Source context selection failed: {error}"),
                        );
                        return None;
                    }
                }
                Some(target)
            })
            .collect();
        self.restore_typing_environment(previous);
        result
    }
    pub(super) fn begin_source_argument(
        &mut self,
        event: CopyCallEventId,
        slot: usize,
        syntax: &Expr,
        frame: &Frame,
    ) -> usize {
        let marker = self.call_input_source.operands.len();
        let context = self.invocation_context(frame.callable_owner);
        self.call_input_source.operands.push(Operand {
            source_id: syntax.hir_id,
            context,
            event,
            slot: slot as u32,
        });
        marker
    }

    pub(super) fn source_argument_of(
        &self,
        syntax: &Expr,
        frame: &Frame,
    ) -> Option<(CopyCallEventId, u32)> {
        let operand = self.call_input_source.operands.last()?;
        (operand.source_id.is_some()
            && operand.source_id == syntax.hir_id
            && operand.context == self.invocation_context(frame.callable_owner))
        .then_some((operand.event, operand.slot))
    }

    pub(super) fn end_source_argument(&mut self, marker: usize) {
        self.call_input_source.operands.truncate(marker);
    }

    /// Capture the exact completed child before any later operand can execute.
    /// The packet's birth coordinates remain immutable if this query probes a
    /// callable and advances heap recency.
    pub(super) fn capture_evaluation_source(
        &mut self,
        packet: &mut EvaluatedValue,
        syntax: &Expr,
        frame: &Frame,
        mut lease: crate::sema::application_effect::WorkLease,
    ) {
        enum Capture {
            Ordinary(CapturedSource),
            Numeric {
                hole: ril_compiler_core::ids::NumericHoleId,
                birth: crate::sema::numeric_selection::NumericBirth,
                environment: crate::sema::context::FrozenEnvId,
            },
        }
        if let Err(error) = packet.preflight_source_capture() {
            if let Err(error) = self.application_effect.return_work(lease) {
                packet.fail_current_source(error);
            }
            packet.fail_current_source(error);
            self.unsupported(
                syntax.span,
                "evaluation Source basis is not eligible for capture",
            );
            return;
        }
        let mut fresh = None;
        let mut stage = "physical observation";
        let work = lease.work();
        let mut capture = (|| {
            work.charge(4)?;
            let observation = packet.observation.ok_or(SourceTypesError::MissingNode)?;
            let fact = self
                .application_effect
                .expressions
                .get(observation)
                .ok_or(SourceTypesError::MissingNode)?;
            let record = self
                .application_effect
                .evaluations
                .get(observation)
                .ok_or(SourceTypesError::MissingNode)?;
            let identity = record.identity.ok_or(SourceTypesError::MissingNode)?;
            let environment = record.environment.ok_or(SourceTypesError::MissingNode)?;
            let birth_environment = self
                .type_source
                .storage
                .live_types()
                .environment(environment, work)?;
            let activation = self
                .application_effect
                .activations
                .get(identity.activation.0 as usize)
                .ok_or(SourceTypesError::MissingNode)?;
            let written_resume = matches!(
                syntax.kind,
                ExprKind::Control {
                    operation: ControlOperation::Resume,
                    ..
                }
            );
            let original_resume =
                self.semantic_hir
                    .expression(identity.source)
                    .is_some_and(|node| {
                        matches!(
                            node.kind,
                            crate::hir::nodes::ExprKind::Control {
                                operation: ControlOperation::Resume,
                                ..
                            }
                        )
                    });
            if written_resume != original_resume {
                return Err(SourceTypesError::Unresolved);
            }
            let expected_kind = if written_resume {
                crate::sema::application_effect::ActivationKind::ControlTransfer
            } else {
                crate::sema::application_effect::ActivationKind::Expression
            };
            if syntax.hir_id != Some(identity.source)
                || fact.source_id != syntax.hir_id
                || record.id.0 as usize != observation
                || packet.identity != Some(identity)
                || packet.birth_context != Some(record.context)
                || packet.environment != Some(environment)
                || record.context != self.invocation_context(frame.callable_owner)
                || activation.result != Some(record.id)
                || activation.kind != expected_kind
                || activation.scope != record.scope
                || record.allocation_epoch != packet.allocation_epoch
                || fact.allocation_epoch != packet.allocation_epoch
            {
                return Err(SourceTypesError::Unresolved);
            }
            let mut equality_work = work.remaining();
            let before_equality = equality_work;
            let same = crate::sema::evaluated::same_birth_value(
                &fact.value,
                &packet.value,
                &mut equality_work,
            );
            work.charge(before_equality - equality_work)?;
            if !same? {
                return Err(SourceTypesError::Unresolved);
            }
            stage = "construction";
            let mut remaining = work.remaining();
            let before = remaining;
            let construction = source_reception::construction(syntax, &mut remaining);
            work.charge(before - remaining)?;
            fresh = Some(std::sync::Arc::new(
                construction.ok_or(SourceTypesError::BudgetExceeded)?,
            ));
            stage = "original Source query";
            let source = self.with_typing_environment(&birth_environment, |checker| {
                checker.original_source_receiving_schema_at(
                    &packet.value,
                    syntax,
                    frame,
                    work,
                    Some(observation),
                )
            })?;
            if source.is_none()
                && let Ty::NumericHole(hole) = packet.value.ty
            {
                stage = "numeric birth";
                let birth = self.pending_numeric_packet_birth(packet, hole, work)?;
                Ok(Capture::Numeric {
                    hole,
                    birth,
                    environment,
                })
            } else {
                stage = "Source interning";
                let captured = if let Some((schema, environment)) = source {
                    CapturedSource::Known(SourceRef::intern(
                        &schema,
                        environment,
                        self.type_source.storage.live_types_mut(),
                        work,
                    )?)
                } else {
                    CapturedSource::Unknown(environment)
                };
                Ok(Capture::Ordinary(captured))
            }
        })();
        // Do not publish an apparently successful basis until all nested
        // recorder work has completed under the same original allowance.
        if let Err(error) = self.application_effect.return_work(lease) {
            capture = Err(error);
        }
        let failure = capture.as_ref().err().cloned();
        if let Err(error) = &capture {
            self.unsupported(
                syntax.span,
                format!(
                    "evaluation Source capture failed at {stage}: {error}; observation={:?} HIR={:?}",
                    packet.observation, packet.identity
                ),
            );
        }
        let captured = match capture {
            Ok(Capture::Numeric {
                hole,
                birth,
                environment,
            }) => packet.capture_numeric_birth_source(hole, birth, environment, fresh),
            result => packet.capture_birth_source(
                result.map(|capture| match capture {
                    Capture::Ordinary(source) => source,
                    Capture::Numeric { .. } => unreachable!("numeric capture handled above"),
                }),
                fresh,
            ),
        };
        if let Some(error) = failure {
            packet.fail_current_source(error);
        }
        if let Err(error) = captured {
            self.unsupported(
                syntax.span,
                format!("evaluation Source basis could not be captured: {error}"),
            );
        }
    }

    /// Map the existing frozen packet to its actual public parameter slot.
    pub(super) fn publish_numeric_call_input(
        &mut self,
        event: CopyCallEventId,
        preparation: usize,
        slot: usize,
        packet: std::sync::Arc<EvaluatedValue>,
        frame: &Frame,
    ) -> Result<(), SourceTypesError> {
        if !self.application_effect.admit(8) {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let (hole, birth, resolution) = packet
            .numeric_source_derivation()
            .ok_or(SourceTypesError::Unresolved)?;
        let row = self
            .call_arguments
            .get(preparation)
            .ok_or(SourceTypesError::MissingNode)?;
        let token = row
            .supplied
            .get(&(slot as u32))
            .ok_or(SourceTypesError::MissingNode)?;
        let numeric = self
            .numeric
            .holes
            .get(hole.0 as usize)
            .filter(|record| record.id == hole)
            .ok_or(SourceTypesError::MissingNode)?;
        let fact = self
            .application_effect
            .expressions
            .get(token.expression)
            .ok_or(SourceTypesError::MissingNode)?;
        if row.source_event != event
            || !row.slots_bound
            || row.slots.get(slot) != Some(&crate::sema::default_uses::ArgumentSource::Supplied)
            || packet.observation != Some(token.expression)
            || packet.allocation_epoch != token.allocation_epoch
            || numeric.birth != *birth
            || !std::sync::Arc::ptr_eq(self.numeric.resolution(hole)?, resolution)
            || fact.value.ty != Ty::NumericHole(hole)
        {
            return Err(SourceTypesError::Unresolved);
        }
        let context = self.invocation_context(frame.callable_owner);
        let input = self
            .call_input_source
            .supplied
            .get_mut(&event)
            .and_then(|inputs| inputs.get_mut(&slot))
            .ok_or(SourceTypesError::MissingNode)?;
        if input.context != context
            || input.default.is_some()
            || !input.packet.shares_birth(&packet)
        {
            return Err(SourceTypesError::Unresolved);
        }
        input.packet = packet;
        Ok(())
    }

    /// Map the existing frozen packet to its actual public parameter slot.
    pub(super) fn bind_call_input_source(
        &mut self,
        event: CopyCallEventId,
        role: EvaluationRole,
        slot: usize,
        packet: std::sync::Arc<EvaluatedValue>,
        frame: &Frame,
    ) -> bool {
        let Some(expression) = packet.observation else {
            return false;
        };
        let context = self.invocation_context(frame.callable_owner);
        if packet.birth_context != Some(context) {
            return false;
        }
        let mut rows = self
            .call_arguments
            .iter()
            .filter(|row| row.source_event == event);
        let Some(preparation) = rows.next() else {
            return false;
        };
        if rows.next().is_some()
            || !preparation.evaluated.iter().any(|child| {
                child.role == role
                    && child.observation.expression == expression
                    && child.observation.allocation_epoch == packet.allocation_epoch
            })
        {
            return false;
        }
        let Some(row) = self.application_effect.contexts.get_mut(expression) else {
            return false;
        };
        let mapped = (event, slot as u32);
        if row.expression != expression
            || row.context != context
            || row.argument_of.is_some_and(|old| old != mapped)
        {
            return false;
        }
        row.argument_of = Some(mapped);
        self.call_input_source
            .supplied
            .entry(event)
            .or_default()
            .insert(
                slot,
                Input {
                    context,
                    packet,
                    default: None,
                },
            )
            .is_none()
    }

    pub(super) fn record_default_call_input_source(
        &mut self,
        event: CopyCallEventId,
        slot: usize,
        id: DefaultUseId,
        syntax: &Expr,
        frame: &Frame,
        packet: std::sync::Arc<EvaluatedValue>,
    ) {
        let Some(record) = self
            .default_uses
            .get(id.0 as usize)
            .filter(|record| record.id == id)
        else {
            return;
        };
        let Some(root) = record.result_expression else {
            return;
        };
        let mut context = self.invocation_context(frame.callable_owner);
        context.default_use = Some(id);
        if packet.observation != Some(root)
            || packet.birth_context != Some(context)
            || packet.identity.map(|identity| identity.source) != syntax.hir_id
            || record
                .result_allocation_epoch
                .is_none_or(|epoch| epoch < packet.allocation_epoch)
        {
            self.unsupported(
                syntax.span,
                "default Source packet lost its original DefaultUse birth",
            );
            return;
        }
        let caller = record.caller;
        self.call_input_source.defaults.insert(
            (event, slot),
            Input {
                context: caller,
                packet,
                default: Some(id),
            },
        );
    }

    pub(super) fn call_supplied_observations(
        &self,
        event: CopyCallEventId,
    ) -> BTreeMap<u32, crate::sema::default_uses::SuppliedArgument> {
        self.call_input_source
            .supplied
            .get(&event)
            .into_iter()
            .flat_map(|arguments| arguments.iter())
            .filter_map(|(slot, input)| {
                Some((
                    *slot as u32,
                    crate::sema::default_uses::SuppliedArgument {
                        expression: input.observation?,
                        allocation_epoch: input.allocation_epoch,
                    },
                ))
            })
            .collect()
    }

    pub(super) fn check_named_input_source(
        &mut self,
        info: &FunctionInfo,
        slot: usize,
        packet: &EvaluatedValue,
        source_event: Option<CopyCallEventId>,
        span: Span,
    ) -> bool {
        let value = packet.value();
        let Some(syntax) = info
            .syntax
            .parameters
            .get(slot)
            .and_then(|parameter| parameter.ty.as_ref())
        else {
            return true;
        };
        let target = self.freeze_source_receiving_target(syntax);
        if target.sensitivity == source_reception::SchemaSensitivity::NotRequired {
            return true;
        }
        let expected = (|| {
            let schema = target.schema.as_ref().ok_or(SourceTypesError::Unresolved)?;
            let selected = self.actual_input_source_schemas(
                info.definition,
                source_event,
                span,
                &mut WorkLimit::new(16384),
            )?;
            schema.substitute(&selected, &mut WorkLimit::new(16384))
        })();
        let expected = match expected {
            Ok(schema) => schema,
            Err(error) => {
                self.unsupported(
                    span,
                    format!("call input requires its complete formal source schema: {error}"),
                );
                return false;
            }
        };
        if matches!(
            expected.sensitivity(&mut WorkLimit::new(16384)),
            crate::sema::source_types::SourceSensitivity::Absent { .. }
        ) {
            return true;
        }
        let input = source_event
            .and_then(|event| {
                self.call_input_source
                    .supplied
                    .get(&event)
                    .and_then(|arguments| arguments.get(&slot))
                    .or_else(|| self.call_input_source.defaults.get(&(event, slot)))
            })
            .cloned();
        let answer = if source_event.is_none() {
            self.generated_entry_source_schema(slot)
                .and_then(|source| match source {
                    Some(source) => Ok(Some(source)),
                    None => self.signature_entry_source_schema(slot),
                })
                .and_then(|source| {
                    expected.receive_schema(
                        &source.ok_or(SourceTypesError::Unresolved)?.0,
                        Some(&Construction::Opaque),
                        &mut WorkLimit::new(16384),
                    )
                })
        } else {
            input
                .as_ref()
                .and_then(|input| {
                    let event = source_event
                        .and_then(|event| self.copy_call_events.get(event.0 as usize))?;
                    if let Some(id) = input.default {
                        let record = self
                            .default_uses
                            .get(id.0 as usize)
                            .filter(|record| record.id == id)?;
                        if record.target != Some(info.definition)
                            || record.parameter as usize != slot
                            || record.caller != input.context
                            || record
                                .result_allocation_epoch
                                .is_none_or(|epoch| epoch < input.allocation_epoch)
                        {
                            return None;
                        }
                        match record.origin {
                            crate::sema::default_uses::DefaultOrigin::Call(id)
                                if id == event.id
                                    && event.owner == input.context.owner
                                    && event.parent == input.context.invocation => {}
                            crate::sema::default_uses::DefaultOrigin::InvocationFallback(id)
                                if self.copy_invocation_stack.last() == Some(&id)
                                    && self.copy_invocations.get(id.0 as usize).is_some_and(
                                        |call| {
                                            call.source_event == Some(event.id)
                                                && call.target == info.definition
                                        },
                                    ) => {}
                            _ => return None,
                        }
                    } else if event.owner != input.context.owner
                        || event.parent != input.context.invocation
                    {
                        return None;
                    }
                    input.packet.shares_birth(packet).then(|| input.clone())
                })
                .ok_or(SourceTypesError::MissingNode)
                .and_then(|_input| {
                    input_compatible(
                        &expected,
                        packet,
                        SourceTypesRef::Live(self.type_source.storage.live_types()),
                        &mut WorkLimit::new(16384),
                    )
                })
        };
        match answer {
            Ok(true) => true,
            Ok(false) => {
                self.error(
                    "E0301",
                    span,
                    "original input array or callable source schema does not fit the parameter",
                    [value.cause],
                );
                false
            }
            Err(error) => {
                self.unsupported(
                    span,
                    format!("call input lacks its original complete schema and actual Source observation: {error}"),
                );
                false
            }
        }
    }

    fn generated_entry_source_schema(&mut self, slot: usize) -> InputSource {
        let Some(id) = self.copy_invocation_stack.last() else {
            return Ok(None);
        };
        let call = self
            .copy_invocations
            .get(id.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        let origin = self
            .application_effect
            .snapshot_origin(&call.entry.origin)
            .ok_or(SourceTypesError::BudgetExceeded)?;
        self.generated_input_source_schema(&origin, slot)
    }

    pub(in crate::sema::checker) fn generated_input_source_schema(
        &mut self,
        origin: &crate::sema::application_effect::EntryOrigin,
        slot: usize,
    ) -> InputSource {
        use crate::sema::application_effect::{EntryOrigin, InputOrigin};
        let EntryOrigin::Generated { inputs, .. } = origin else {
            return Ok(None);
        };
        let (observation, boundary) = match inputs.get(slot).ok_or(SourceTypesError::MissingNode)? {
            InputOrigin::Scope(_) => {
                return self.input_header_schema(
                    &ArgumentKey::Name {
                        name: "Concurrent::Scope".into(),
                        arguments: vec![],
                    },
                    None,
                    crate::sema::context::FrozenEnvironment::default(),
                    &mut WorkLimit::new(16384),
                );
            }
            InputOrigin::Copied {
                observation,
                boundary,
            } => (*observation, Some(*boundary)),
            InputOrigin::Observed(observation) | InputOrigin::Widened(observation) => {
                (*observation, None)
            }
            InputOrigin::Scalar(kind) => {
                let key = ArgumentKey::Name {
                    name: match kind {
                        crate::sema::application_effect::ScalarInput::PositiveInt => "int",
                        crate::sema::application_effect::ScalarInput::ByteSuffix(_)
                        | crate::sema::application_effect::ScalarInput::BufferedBytes(_) => "bytes",
                    }
                    .into(),
                    arguments: vec![],
                };
                return self.input_header_schema(
                    &key,
                    None,
                    self.capture_typing_environment(),
                    &mut WorkLimit::new(16384),
                );
            }
        };
        let original = self
            .application_effect
            .expressions
            .get(observation.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        let source = original.source_id.ok_or(SourceTypesError::MissingNode)?;
        let node = self
            .semantic_hir
            .expression(source)
            .ok_or(SourceTypesError::MissingNode)?;
        let mut work = WorkLimit::new(16384);
        work.charge(
            self.call_input_source
                .supplied
                .values()
                .map(BTreeMap::len)
                .sum::<usize>()
                + self.call_input_source.defaults.len(),
        )?;
        let mut captured = self
            .call_input_source
            .supplied
            .values()
            .flat_map(BTreeMap::values)
            .chain(self.call_input_source.defaults.values())
            .filter(|input| input.observation == Some(observation.0 as usize));
        let first = captured.next();
        let captured_source = first.map(|input| {
            input
                .input_source(
                    SourceTypesRef::Live(self.type_source.storage.live_types()),
                    &mut work,
                )
                .map(|source| source.into_known())
        });
        if captured.any(|input| {
            !first.is_some_and(|first| std::sync::Arc::ptr_eq(&first.packet, &input.packet))
        }) {
            return Err(SourceTypesError::Unresolved);
        }
        let source = if let Some(captured) = captured_source {
            captured?
        } else if let Some(stored) =
            self.generated_observation_source_schema(observation, &mut work)
        {
            stored?
        } else {
            let stored = if let crate::hir::nodes::ExprKind::Name(name) = &node.kind
                && original.value.sources.len() == 1
                && let Some(binding) = original.value.sources.first()
                && self
                    .bindings
                    .get(*binding)
                    .is_some_and(|binding| binding.name == *name)
            {
                self.recorded_binding_source_schema(*binding, &mut work)
            } else {
                None
            };
            if let Some(source) = stored {
                source?
                    .map(|(schema, environment)| {
                        use crate::sema::source_types::projection_receipts::ProjectionOccurrence;
                        let record = self
                            .application_effect
                            .evaluations
                            .get(observation.0 as usize)
                            .ok_or(SourceTypesError::MissingNode)?;
                        let occurrence = ProjectionOccurrence {
                            identity: record.identity.ok_or(SourceTypesError::MissingNode)?,
                            context: record.context,
                            cause: original.value.cause,
                        };
                        let depth = self
                            .source_projection_receipts()
                            .unwrap_depth(occurrence, &mut work)?;
                        let schema = if depth == 1 {
                            schema.project_steps(
                                &[crate::sema::source_types::SourcePath::OptionalPayload],
                                &mut work,
                            )?
                        } else {
                            schema
                        };
                        Ok((schema, environment))
                    })
                    .transpose()?
            } else if let Some(schema) =
                crate::sema::source_types::declarations::construction_schema(
                    source,
                    &self.semantic_hir,
                    &mut work,
                )?
            {
                Some((schema, self.capture_typing_environment()))
            } else if let Some(witness) = &original.value.source_type_witness {
                if !witness.validate_closed() {
                    return Err(SourceTypesError::Unresolved);
                }
                let key = crate::static_eval::effects::bounded_argument_key(
                    &witness.syntax,
                    &BTreeMap::new(),
                )
                .ok_or(SourceTypesError::BudgetExceeded)?;
                self.input_header_schema(
                    &key,
                    witness.syntax.hir_id,
                    self.capture_typing_environment(),
                    &mut work,
                )?
            } else {
                None
            }
        };
        source
            .map(|(schema, environment)| {
                let schema = if let Some(boundary) = boundary {
                    let proof = self
                        .copy_boundaries
                        .get(boundary.0 as usize)
                        .filter(|proof| proof.id == boundary)
                        .ok_or(SourceTypesError::MissingNode)?;
                    schema.copy_view(proof.mode, &mut work)?
                } else {
                    schema
                };
                Ok((schema, environment))
            })
            .transpose()
    }

    fn signature_entry_source_schema(&mut self, slot: usize) -> InputSource {
        let Some(id) = self.copy_invocation_stack.last() else {
            return Ok(None);
        };
        let call = self
            .copy_invocations
            .get(id.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        if !matches!(
            call.entry.origin,
            crate::sema::application_effect::EntryOrigin::SignatureProbe(_)
        ) {
            return Ok(None);
        }
        let crate::sema::application_effect::EntryOrigin::SignatureProbe(source) =
            &call.entry.origin
        else {
            unreachable!()
        };
        let source = source.clone();
        let input = call
            .entry
            .arguments
            .get(slot)
            .ok_or(SourceTypesError::MissingNode)?;
        let schema = source.parameter_schema(slot, input.mode, &mut WorkLimit::new(16384))?;
        self.selected_input_schema(
            schema,
            source.environment.clone(),
            &mut WorkLimit::new(16384),
        )
        .map(Some)
    }
    pub(super) fn check_public_call_input_sources(
        &mut self,
        callee: &Value,
        syntax: &Expr,
        event: CopyCallEventId,
        frame: &Frame,
    ) {
        if matches!(callee.callables.as_slice(), [Callable::Named(_)])
            || callee
                .callables
                .iter()
                .all(|callable| matches!(callable, Callable::Builtin(_) | Callable::Constructor(_)))
        {
            return;
        }
        let parameters = match self.public_input_source_schemas(callee, syntax, frame) {
            Ok(Some(parameters)) => parameters,
            Ok(None) => {
                self.unsupported(
                    syntax.span,
                    "public callable input requires its original complete Source signature",
                );
                return;
            }
            Err(error) => {
                self.unsupported(
                    syntax.span,
                    format!("public callable input Source signature failed: {error}"),
                );
                return;
            }
        };
        let context = self.invocation_context(frame.callable_owner);
        for (slot, expected) in parameters.iter().enumerate() {
            let Some(expected) = expected else { continue };
            if matches!(
                expected.sensitivity(&mut WorkLimit::new(16384)),
                crate::sema::source_types::SourceSensitivity::Absent { .. }
            ) {
                continue;
            }
            let input = self
                .call_input_source
                .supplied
                .get(&event)
                .and_then(|rows| rows.get(&slot))
                .or_else(|| self.call_input_source.defaults.get(&(event, slot)))
                .cloned();
            let answer = input
                .as_ref()
                .ok_or(SourceTypesError::MissingNode)
                .and_then(|input| {
                    if input.context != context {
                        return Err(SourceTypesError::Unresolved);
                    }
                    input_compatible(
                        expected,
                        input,
                        SourceTypesRef::Live(self.type_source.storage.live_types()),
                        &mut WorkLimit::new(16384),
                    )
                });
            match answer {
                Ok(true) => {},
                Ok(false) => self.error("E0301", syntax.span,
                    "original input source does not fit the actual public callable signature", [callee.cause]),
                Err(error) => self.unsupported(syntax.span,
                    format!("public callable input lost its complete original schema or actual operand identity: {error}")),
            }
        }
    }

    fn public_input_source_schemas(
        &mut self,
        callee: &Value,
        syntax: &Expr,
        frame: &Frame,
    ) -> Result<Option<Vec<Option<SourceSchema>>>, SourceTypesError> {
        // A sealed public view has priority over an underlying inferred lambda.
        let mut work = WorkLimit::new(16384);
        if let Some((source, _)) =
            self.original_source_receiving_schema(callee, syntax, frame, &mut work)?
        {
            return source.callable_parameters(&mut work).map(|parameters| {
                Some(
                    parameters
                        .into_iter()
                        .map(|(_, schema)| Some(schema))
                        .collect(),
                )
            });
        }
        if callee.callables.is_empty() {
            return Ok(None);
        }
        let mut common: Option<Vec<Option<SourceSchema>>> = None;
        for callable in &callee.callables {
            let keys = match callable {
                Callable::Closure(index) => {
                    let closure = self
                        .closures
                        .get(*index)
                        .ok_or(SourceTypesError::MissingNode)?
                        .clone();
                    let contract = self
                        .lambda_contract(*index)
                        .ok_or(SourceTypesError::MissingNode)?
                        .clone();
                    let previous = self.enter_typing_environment(&contract.typing_environment);
                    let keys: Result<Vec<_>, SourceTypesError> = closure
                        .parameters
                        .iter()
                        .map(|parameter| match &parameter.ty {
                            None => Ok(None),
                            Some(syntax) => {
                                let target = self.freeze_source_receiving_target(syntax);
                                if target.sensitivity
                                    == source_reception::SchemaSensitivity::NotRequired
                                {
                                    Ok(None)
                                } else {
                                    target.schema.map(Some).ok_or(SourceTypesError::Unresolved)
                                }
                            }
                        })
                        .collect();
                    self.restore_typing_environment(previous);
                    keys?
                }
                Callable::Symbolic(..) if self.symbolic_has_no_inputs(callee) => Vec::new(),
                _ => return Ok(None),
            };
            if let Some(previous) = common.as_ref()
                && !input_schema_lists_agree(previous, &keys, &mut work)?
            {
                return Err(SourceTypesError::Unresolved);
            }
            common = Some(keys);
        }
        Ok(common)
    }

    fn symbolic_has_no_inputs(&mut self, callee: &Value) -> bool {
        let sources: BTreeSet<_> = callee
            .callback_parameters
            .union(&callee.sources)
            .copied()
            .collect();
        !sources.is_empty()
            && sources.iter().all(|id| {
                let Some(binding) = self.bindings.get(*id) else {
                    return false;
                };
                if !binding.parameter {
                    return false;
                }
                let parameters: Vec<_> = self
                    .functions
                    .iter()
                    .flat_map(|function| function.syntax.parameters.iter())
                    .filter(|parameter| parameter.pattern.span == binding.span)
                    .collect();
                let [parameter] = parameters.as_slice() else {
                    return false;
                };
                let Some(mut syntax) = parameter.ty.as_ref() else {
                    return false;
                };
                if let TypeKind::Optional(inner) = &syntax.kind {
                    syntax = inner;
                }
                matches!(&syntax.kind,TypeKind::Callable {parameters,..} if parameters.is_empty())
            })
    }

    pub(super) fn require_recorded_public_call_inputs(
        &mut self,
        callee: &Value,
        span: Span,
        frame: &Frame,
    ) {
        if frame.copy_call_event.is_some()
            || callee.callables.iter().all(|callable| {
                matches!(
                    callable,
                    Callable::Named(_) | Callable::Builtin(_) | Callable::Constructor(_)
                )
            })
        {
            return;
        }
        // A pipeline/internal callback has no ordinary operand receipt. Written
        // scalar inputs remain ordinary; arrays and Fn inputs require the real
        // caller boundary rather than borrowing a surrounding call's event.
        let sensitive = callee.signature.as_ref().is_some_and(|signature| {
            self.with_typing_environment(&signature.environment, |checker| {
                signature
                    .parameters
                    .iter()
                    .filter_map(|parameter| parameter.ty.as_ref())
                    .any(|syntax| {
                        checker.freeze_source_receiving_target(syntax).sensitivity
                            != source_reception::SchemaSensitivity::NotRequired
                    })
            })
        });
        if sensitive {
            self.unsupported(
                span,
                "a sensitive public callable input requires its actual operand Source receipt",
            );
        }
    }
}

fn input_compatible(
    expected: &SourceSchema,
    input: &EvaluatedValue,
    types: SourceTypesRef<'_>,
    work: &mut WorkLimit,
) -> Result<bool, SourceTypesError> {
    match input
        .input_source(types, work)
        .map(|source| source.into_known())
    {
        Ok(Some((actual, environment))) if !environment.is_poisoned() => {
            expected.receive_schema(&actual, Some(input.fresh()), work)
        }
        Ok(None) => expected
            .empty_context(input.fresh(), work)?
            .ok_or(SourceTypesError::Unresolved),
        Ok(Some(_)) => Err(SourceTypesError::Unresolved),
        Err(error) => Err(error.clone()),
    }
}

fn input_schema_lists_agree(
    left: &[Option<SourceSchema>],
    right: &[Option<SourceSchema>],
    work: &mut WorkLimit,
) -> Result<bool, SourceTypesError> {
    work.charge(left.len() + right.len())?;
    if left.len() != right.len() {
        return Ok(false);
    }
    for (left, right) in left.iter().zip(right) {
        match (left, right) {
            (Some(left), Some(right)) if left.equivalent(right, work)? => {}
            (None, None) => {}
            _ => return Ok(false),
        }
    }
    Ok(true)
}

#[cfg(test)]
fn select(
    key: &ArgumentKey,
    selected: &BTreeMap<String, ArgumentKey>,
    work: &mut usize,
    depth: usize,
) -> Option<ArgumentKey> {
    if depth >= 64 {
        return None;
    }
    let mut budget = crate::sema::source_types::WorkLimit::new(*work);
    let result = crate::sema::source_types::substitute_key_with(
        key,
        |name, _| Ok(selected.get(name).map(std::borrow::Cow::Borrowed)),
        &mut budget,
    );
    *work = budget.remaining();
    result.ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_immutable_tuple_fields_keep_their_complete_schema() {
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let source = ril_test::case_source(
                    "tests/regressions/record-bounds.ril::scoped-immutable-field",
                );
                let parsed = ril_syntax::parse(source);
                assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
                let mut checker = Checker::new(FileId(0));
                checker.run(&parsed.program);
                let mut expected = Vec::new();
                for call in &checker.copy_invocations {
                    let Some(function) = checker
                        .functions
                        .iter()
                        .find(|function| function.definition == call.target)
                    else {
                        continue;
                    };
                    let scope: BTreeMap<_, _> = function
                        .typing_environment
                        .generic_context
                        .iter()
                        .map(|(name, id)| (name.clone(), id.clone()))
                        .chain(
                            checker
                                .generic_binders
                                .values()
                                .filter(|binder| binder.definition == call.target)
                                .map(|binder| (binder.name.clone(), binder.identity.clone())),
                        )
                        .collect();
                    let selected: BTreeMap<_, _> = checker
                        .effect_invocations
                        .iter()
                        .filter(|row| row.invocation == Some(call.id))
                        .flat_map(|row| &row.arguments)
                        .filter_map(|argument| {
                            Some((argument.binder.clone(), argument.key.clone()?))
                        })
                        .collect();
                    for parameter in &function.syntax.parameters {
                        if let Some(key) = parameter.ty.as_ref().and_then(|syntax| {
                            crate::static_eval::effects::bounded_argument_key(syntax, &scope)
                        }) {
                            expected.push((
                                function.syntax.name.clone(),
                                call.span,
                                select(&key, &selected, &mut 4096, 0),
                            ));
                        }
                    }
                }
                assert!(
                    checker.diagnostics.is_empty() && checker.unsupported.is_empty(),
                    "diagnostics={:?}\nunsupported={:?}\nexpected={expected:#?}\nactual={:#?}",
                    checker.diagnostics,
                    checker.unsupported,
                    checker.call_input_source.supplied
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn symbolic_formal_inputs_keep_complete_coordinates_before_reception() {
        std::thread::Builder::new().stack_size(16 * 1024 * 1024).spawn(|| {
        let source = ril_test::case_source("tests/regressions/record-bounds.ril::scoped-symbolic-array-explicit");
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut checker = Checker::new(FileId(0));
        checker.run(&parsed.program);
        let expressions: Vec<_> = checker.application_effect.contexts.iter().filter_map(|row| {
            let fact = checker.application_effect.expressions.get(row.expression)?;
            (fact.span.start == 49 || fact.span.start == 126).then(||
                (row.context, fact.span, fact.value.ty.clone(), fact.value.cause,
                    checker.explanations.causes.get(fact.value.cause.0 as usize).map(|cause| cause.parents.clone()),
                    fact.value.source_type_witness.clone()))
        }).collect();
        let projections: Vec<_> = checker.generic_bound_projections.iter().map(|projection|
            (projection.context, projection.span, projection.output.value.cause, projection.output.value.ty.clone())).collect();
        assert!(
            checker.diagnostics.is_empty() && checker.unsupported.is_empty(),
            "diagnostics={:?}\nunsupported={:?}\noriginal inputs={:?}\nexpressions={expressions:?}\nprojections={projections:?}",
            checker.diagnostics,
            checker.unsupported,
            checker.call_input_source.supplied
        );
        }).unwrap().join().unwrap();
    }
}
