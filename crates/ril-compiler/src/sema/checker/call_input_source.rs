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
    source_reception::{self, Construction},
    source_types::{SourceSchema, SourceTypesError, WorkLimit},
};
#[path = "closure_parameter_sources.rs"]
mod closure_parameters;
#[path = "call_input_source_closures.rs"]
mod closure_sources;
#[path = "call_input_source_composites.rs"]
mod composites;
#[path = "constructor_input_source.rs"]
mod constructor_inputs;
#[path = "call_input_source_graph.rs"]
mod graph_sources;
#[path = "call_input_source_headers.rs"]
mod headers;
#[path = "call_input_source_result.rs"]
mod producing_result;
#[path = "storage_input_source.rs"]
mod storage_inputs;

#[derive(Clone, Debug)]
struct Input {
    context: InvocationContext,
    expression: Option<usize>,
    allocation_epoch: usize,
    source: InputSource,
    fresh: Construction,
    default: Option<DefaultUseId>,
}

#[derive(Default)]
pub(super) struct State {
    evaluated: BTreeMap<(CopyCallEventId, EvaluationRole), Input>,
    supplied: BTreeMap<CopyCallEventId, BTreeMap<usize, Input>>,
    defaults: BTreeMap<(CopyCallEventId, usize), Input>,
    operands: Vec<Operand>,
    carriers: BTreeMap<u32, (CopyCallEventId, InvocationContext)>,
    carrier_sources: BTreeMap<u32, (SourceSchema, FrozenEnvironment)>,
    closure_views: BTreeMap<usize, (u32, SourceSchema, FrozenEnvironment)>,
}

type InputSource = Result<Option<(SourceSchema, FrozenEnvironment)>, SourceTypesError>;

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
            .source
            .clone()
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
            .and_then(|input| input_compatible(expected, input, &mut WorkLimit::new(16384)));
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
        let (actual, actual_environment) = match &input.source {
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
        let observation = input.expression?;
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
        let mut work = WorkLimit::new(16384);
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
        let agrees = match schema.equivalent(actual, &mut work) {
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
    pub(super) fn evaluated_argument_source(
        &self,
        event: CopyCallEventId,
        role: EvaluationRole,
    ) -> Option<&InputSource> {
        Some(&self.call_input_source.evaluated.get(&(event, role))?.source)
    }
    pub(super) fn remember_result_carrier(
        &mut self,
        callee: &Value,
        value: &Value,
        event: Option<CopyCallEventId>,
        frame: &Frame,
    ) {
        if let Some(event) = event
            && matches!(callee.callables.as_slice(),[Callable::Builtin(name)] if matches!(name.as_str(),"Ok"|"Err"|"Prelude::Ok"|"Prelude::Err"))
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

    pub(super) fn capture_call_input_source(
        &mut self,
        event: CopyCallEventId,
        role: EvaluationRole,
        syntax: &Expr,
        observed: Option<usize>,
        frame: &Frame,
    ) {
        let Some(expression) = observed else {
            return;
        };
        let Some(observation) = self.application_effect.expressions.get(expression) else {
            return;
        };
        let context = self.invocation_context(frame.callable_owner);
        if (observation.source_id.is_none() || observation.source_id != syntax.hir_id)
            || !self
                .application_effect
                .contexts
                .get(expression)
                .is_some_and(|row| row.expression == expression && row.context == context)
        {
            return;
        }
        let observations: Vec<_> = self
            .call_arguments
            .iter()
            .filter(|preparation| preparation.source_event == event)
            .flat_map(|preparation| preparation.evaluated.iter())
            .filter(|evaluated| {
                evaluated.role == role && evaluated.observation.expression == expression
            })
            .collect();
        let [evaluated] = observations.as_slice() else {
            return;
        };
        let allocation_epoch = evaluated.observation.allocation_epoch;
        if allocation_epoch != self.recency_moves.len() {
            return;
        }
        let value = observation.value.clone();
        let Some(fresh) = source_reception::construction(syntax, &mut 4096) else {
            self.unsupported(
                syntax.span,
                "call input literal source exceeds its work bound",
            );
            return;
        };
        let source = self.original_source_receiving_schema(
            &value,
            syntax,
            frame,
            &mut WorkLimit::new(16384),
        );
        if let Err(error) = &source {
            self.unsupported(
                syntax.span,
                format!("call input Source capture failed: {error}"),
            );
        }
        self.call_input_source.evaluated.insert(
            (event, role),
            Input {
                context,
                expression: Some(expression),
                allocation_epoch,
                source,
                fresh,
                default: None,
            },
        );
    }

    /// Bind an already evaluated Source; this operation never rereads a Name,
    /// receiver graph, annotation or inferred type after the callee runs.
    pub(super) fn bind_call_input_source(
        &mut self,
        event: CopyCallEventId,
        role: EvaluationRole,
        slot: usize,
        frame: &Frame,
    ) -> bool {
        let Some(input) = self
            .call_input_source
            .evaluated
            .get(&(event, role))
            .cloned()
        else {
            return false;
        };
        let Some(expression) = input.expression else {
            return false;
        };
        if input.context != self.invocation_context(frame.callable_owner) {
            return false;
        }
        let Some(row) = self.application_effect.contexts.get_mut(expression) else {
            return false;
        };
        let mapped = (event, slot as u32);
        if row.expression != expression
            || row.context != input.context
            || row.argument_of.is_some_and(|old| old != mapped)
        {
            return false;
        }
        row.argument_of = Some(mapped);
        self.call_input_source
            .supplied
            .entry(event)
            .or_default()
            .insert(slot, input)
            .is_none()
    }

    pub(super) fn record_default_call_input_source(
        &mut self,
        event: CopyCallEventId,
        slot: usize,
        id: DefaultUseId,
        syntax: &Expr,
        frame: &Frame,
    ) {
        let Some(record) = self
            .default_uses
            .get(id.0 as usize)
            .filter(|record| record.id == id)
        else {
            return;
        };
        let Some(snapshot) = &record.result else {
            return;
        };
        let value = snapshot.value.clone();
        let context = record.caller;
        let Some(root) = record.result_expression else {
            return;
        };
        let mut root_context = self.invocation_context(frame.callable_owner);
        root_context.default_use = Some(id);
        if self
            .application_effect
            .expressions
            .get(root)
            .is_none_or(|fact| fact.source_id != syntax.hir_id || fact.value != value)
            || self
                .application_effect
                .contexts
                .get(root)
                .is_none_or(|row| row.expression != root || row.context != root_context)
        {
            self.unsupported(
                syntax.span,
                "default Source capture lost its original DefaultUse emission",
            );
            return;
        }
        let Some(allocation_epoch) = record.result_allocation_epoch else {
            return;
        };
        let Some(fresh) = source_reception::construction(syntax, &mut 4096) else {
            self.unsupported(
                syntax.span,
                "default input literal source exceeds its work bound",
            );
            return;
        };
        self.default_use_stack.push(id);
        let source = self.original_source_receiving_schema(
            &value,
            syntax,
            frame,
            &mut WorkLimit::new(16384),
        );
        assert_eq!(self.default_use_stack.pop(), Some(id));
        if let Err(error) = &source {
            self.unsupported(
                syntax.span,
                format!("default input Source capture failed: {error}"),
            );
        }
        self.call_input_source.defaults.insert(
            (event, slot),
            Input {
                context,
                expression: None,
                allocation_epoch,
                source,
                fresh,
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
                        expression: input.expression?,
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
        value: &Value,
        source_event: Option<CopyCallEventId>,
        span: Span,
    ) -> bool {
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
                            || record.result_allocation_epoch != Some(input.allocation_epoch)
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
                    Some(input.clone())
                })
                .ok_or(SourceTypesError::MissingNode)
                .and_then(|input| input_compatible(&expected, &input, &mut WorkLimit::new(16384)))
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
        work.charge(self.call_input_source.evaluated.len())?;
        let mut captured = self
            .call_input_source
            .evaluated
            .values()
            .filter(|input| input.expression == Some(observation.0 as usize));
        let captured_source = captured.next().map(|input| input.source.clone());
        if captured.next().is_some() {
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
        let authenticated: crate::sema::application_effect::AuthenticatedSignatureInput<'_> =
            crate::sema::application_effect::signature_assumption(
                call,
                slot,
                &self.semantic_hir,
                &self.bindings,
                self.recency_moves.len(),
                &mut WorkLimit::new(16384),
            )?;
        let header = authenticated.header.clone();
        let environment = authenticated.environment.clone();
        let mode = authenticated.mode;
        let crate::sema::application_effect::EntryOrigin::SignatureProbe(source) =
            &call.entry.origin
        else {
            unreachable!()
        };
        let source = source.clone();
        let root = self.with_typing_environment(&environment, |checker| {
            checker.original_header_source_schema(&header, &mut WorkLimit::new(16384))
        })?;
        let schema = source.parameter_schema(&root, slot, mode, &mut WorkLimit::new(16384))?;
        self.selected_input_schema(schema, environment, &mut WorkLimit::new(16384))
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
                    input_compatible(expected, input, &mut WorkLimit::new(16384))
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
        let sensitive = callee.signature.as_ref().is_some_and(|parameters| {
            parameters
                .iter()
                .filter_map(|parameter| parameter.ty.as_ref())
                .any(|syntax| {
                    self.freeze_source_receiving_target(syntax).sensitivity
                        != source_reception::SchemaSensitivity::NotRequired
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
    input: &Input,
    work: &mut WorkLimit,
) -> Result<bool, SourceTypesError> {
    match &input.source {
        Ok(Some((actual, environment))) if !environment.is_poisoned() => {
            expected.receive_schema(actual, Some(&input.fresh), work)
        }
        Ok(None) => expected
            .empty_context(&input.fresh, work)?
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
    let result = crate::sema::source_types::substitute_key(key, selected, &mut budget);
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
