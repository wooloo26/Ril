//! Original input schemas, before any receiving ascription. Stored array
//! cardinality is deliberately absent; only a real literal AST supplies fresh
//! receiving context. This private state is replayed through CallArguments.
use super::*;
use crate::hir::application::EvaluationRole;
use crate::sema::{
    copy_contract::CopyCallEventId,
    default_uses::DefaultUseId,
    effect_identity::{ArgumentKey, InvocationContext},
    source_reception::{self, Construction},
};
#[path = "call_input_source_closures.rs"]
mod closure_sources;
#[path = "call_input_source_composites.rs"]
mod composites;
#[path = "constructor_input_source.rs"]
mod constructor_inputs;
#[path = "call_input_source_headers.rs"]
mod headers;
#[path = "call_input_source_result.rs"]
mod producing_result;
#[path = "call_input_source_uid.rs"]
mod source_uid;
#[path = "storage_input_source.rs"]
mod storage_inputs;
pub(super) use producing_result::storage_closed_source_syntax;

#[derive(Clone, Debug)]
struct Input {
    context: InvocationContext,
    expression: Option<usize>,
    allocation_epoch: usize,
    key: Option<ArgumentKey>,
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
    carrier_sources: BTreeMap<u32, ArgumentKey>,
    closure_views: BTreeMap<usize, (u32, ArgumentKey)>,
}

struct Operand {
    source_id: Option<ril_compiler_core::ids::ExprId>,
    context: InvocationContext,
    event: CopyCallEventId,
    slot: u32,
}

impl Checker {
    /// This bridge serves only consumers which still require a legacy key.
    /// A graph/export failure is an incomplete analysis, never an unknown view
    /// which can fall back to a later value or another input witness.
    fn input_graph_key(
        &mut self,
        source: Result<Option<ArgumentKey>, crate::sema::source_types::SourceTypesError>,
        span: Span,
    ) -> Option<ArgumentKey> {
        match source {
            Ok(key) => key,
            Err(error) => {
                self.unsupported(
                    span,
                    format!("input Source graph cannot supply its required key view: {error}"),
                );
                None
            }
        }
    }

    pub(super) fn receive_application_source(
        &mut self,
        expected: &ArgumentKey,
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
        let answer = input.as_ref().and_then(|input| {
            if let Some(answer) = source_reception::empty_context(expected, &input.fresh, &mut 4096)
            {
                return Some(answer);
            }
            let actual = input.key.as_ref()?;
            let actual = crate::sema::source_types::declarations::expanded_key(
                actual,
                &self.semantic_hir,
                &mut crate::sema::source_types::WorkLimit::new(16384),
            )
            .ok()?;
            source_reception::compatible(expected, &actual, Some(&input.fresh), &mut 16384)
        });
        match answer {
            Some(true) => true,
            Some(false) => {
                self.error(
                    "E0301",
                    span,
                    "actual input does not fit the declared complete Source view",
                    [value.cause],
                );
                false
            }
            None => {
                self.unsupported(
                    span,
                    "input reception lacks its original complete Source observation",
                );
                false
            }
        }
    }
    pub(super) fn supplied_parameter_source(
        &self,
        slot: usize,
    ) -> Option<std::sync::Arc<crate::sema::source_types::TypeSourceSelection>> {
        use crate::sema::source_types::{SourceSelectionInput, TypeSourceSelection, WorkLimit};
        let invocation = *self.copy_invocation_stack.last()?;
        let call = self.copy_invocations.get(invocation.0 as usize)?;
        let event = call.source_event?;
        let input = self.call_input_source.supplied.get(&event)?.get(&slot)?;
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
        let (schema, original_environment) =
            self.parameter_source_schema(binding, syntax.hir_id)?;
        if environment.id() != original_environment.id()
            || !schema
                .equivalent_key(input.key.as_ref()?, &mut WorkLimit::new(16384))
                .ok()?
        {
            return None;
        }
        TypeSourceSelection::from_parameter(
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
        )
        .ok()
    }
    pub(super) fn evaluated_argument_source(
        &self,
        event: CopyCallEventId,
        role: EvaluationRole,
    ) -> Option<&ArgumentKey> {
        self.call_input_source
            .evaluated
            .get(&(event, role))?
            .key
            .as_ref()
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
        let result = info
            .syntax
            .parameters
            .iter()
            .map(|parameter| {
                let syntax = parameter.ty.as_ref()?;
                let ty = self.ty(syntax);
                let mut names = BTreeSet::new();
                ty.generic_names(&mut names);
                if names.iter().any(|name| {
                    owned.contains(name)
                        && !self
                            .type_source
                            .environment
                            .generic_substitutions
                            .contains_key(name)
                }) {
                    return None;
                }
                let target = self.freeze_source_receiving_target(syntax);
                target.key().as_ref()?;
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

    pub(super) fn original_source_receiving_key(
        &mut self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
    ) -> Option<ArgumentKey> {
        let key = self.raw_original_source_receiving_key(value, syntax, frame)?;
        let context = self.invocation_context(frame.callable_owner);
        let projected = self.invocation_witnesses.iter().any(|row| {
            row.context == context
                && matches!(&row.kind, crate::sema::effect_identity::InvocationWitnessKind::ImplicitUnwrap(proof)
                    if Some(proof.occurrence.source) == syntax.hir_id && proof.cause == value.cause)
        });
        let unwrap = if projected {
            let mut work = crate::sema::source_types::WorkLimit::new(16384);
            let depth = syntax
                .hir_id
                .ok_or(crate::sema::source_types::SourceTypesError::MissingNode)
                .and_then(|source| {
                    self.source_projection_occurrence(source, value, context, &mut work)
                })
                .and_then(|occurrence| {
                    self.source_projection_receipts()
                        .unwrap_depth(occurrence, &mut work)
                });
            match depth {
                Ok(depth) => depth == 1,
                Err(_) => {
                    self.unsupported(
                        syntax.span,
                        "Source projection lost its original optional read occurrence",
                    );
                    return None;
                }
            }
        } else {
            false
        };
        if unwrap
            && let ArgumentKey::Name { name, arguments } = &key
            && name == "Option"
            && arguments.len() == 1
        {
            return Some(arguments[0].clone());
        }
        Some(key)
    }

    fn raw_original_source_receiving_key(
        &mut self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
    ) -> Option<ArgumentKey> {
        self.raw_original_source_receiving_key_inner(value, syntax, frame, &mut 4096, 0)
    }

    fn raw_original_source_receiving_key_inner(
        &mut self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
        work: &mut usize,
        depth: usize,
    ) -> Option<ArgumentKey> {
        *work = work.checked_sub(1)?;
        if depth >= 64 {
            return None;
        }
        if let Some(source) = self.storage_binding_source_schema(value, syntax, frame) {
            let key = source.and_then(|source| source.map(|(schema, _)| schema.key()).transpose());
            return self.input_graph_key(key, syntax.span);
        }
        if let Some(source) = syntax.hir_id {
            let mut limit = crate::sema::source_types::WorkLimit::new(*work);
            let declared = crate::sema::source_types::declarations::construction(
                source,
                &self.semantic_hir,
                &mut limit,
            );
            *work = limit.remaining();
            if let Some(key) = declared.ok()? {
                return Some(key);
            }
        }
        if value.source_type_witness.is_none()
            && matches!(&syntax.kind, ExprKind::Unary { operator, .. } if operator == "^mut")
        {
            return self.original_composite_source_key(value, syntax, frame, work, depth);
        }
        if let Some(key) = self.original_copy_source_key(value, syntax, frame, work, depth) {
            return key;
        }
        if let ExprKind::Name(name) = &syntax.kind
            && self.constant_references.contains_key(name)
        {
            let original = self.constant_source_views.get(name)?;
            if !original.validate_closed() || value.source_type_witness.as_ref() != Some(original) {
                return None;
            }
            return crate::static_eval::effects::bounded_argument_key(
                &original.syntax,
                &BTreeMap::new(),
            );
        }
        if let Some(key) = self.original_carrier_source_key(value, syntax, frame) {
            return Some(key);
        }
        if let Some(key) = self.original_called_result_source(value, syntax, frame) {
            return Some(key);
        }
        if let Some(key) = self.original_symbolic_source_key(value, syntax, frame) {
            return Some(key);
        }
        if let Some(witness) = &value.source_type_witness {
            if !witness.validate_closed() {
                return None;
            }
            return crate::static_eval::effects::bounded_argument_key(
                &witness.syntax,
                &BTreeMap::new(),
            );
        }
        if let Some(key) = self.original_canonical_builtin_source_key(value, syntax, frame) {
            return Some(key);
        }
        if let ExprKind::Name(name) = &syntax.kind {
            let binding = value
                .sources
                .iter()
                .next()
                .and_then(|id| self.bindings.get(*id))?;
            if value.sources.len() != 1 || binding.name != *name {
                return None;
            }
            if binding.parameter {
                return self.formal_source_receiving_key(value, syntax, frame);
            }
            if let [Callable::Named(index)] = value.callables.as_slice() {
                let function = self.functions[*index].clone();
                if binding.parameter
                    || binding.span != function.syntax.span
                    || !function.syntax.generics.is_empty()
                {
                    return None;
                }
                let mut parameters = function.syntax.parameters.clone();
                for parameter in &mut parameters {
                    parameter.default = None;
                }
                let syntax = TypeExpr {
                    hir_id: None,
                    text: String::new(),
                    span: syntax.span,
                    kind: TypeKind::Callable {
                        parameters,
                        result: function.syntax.return_type.clone().map(Box::new),
                        annotations: function.syntax.annotations.clone(),
                    },
                };
                // Array/mode coordinates remain present in the genuine header
                // even if a named obligation row has no closed witness. This
                // does not compare, clear or grant those obligation rows.
                super::source_receiving::resolved_symbolic_names(
                    &syntax,
                    &function.typing_environment.generic_context,
                    &self.types,
                    &mut 4096,
                    0,
                )?;
                return crate::static_eval::effects::bounded_argument_key(
                    &syntax,
                    &function.typing_environment.generic_context,
                );
            }
        }
        if let Some(key) = self.original_composite_source_key(value, syntax, frame, work, depth) {
            return Some(key);
        }
        if let Some(key) = self.original_closure_source_key(value) {
            return Some(key);
        }
        // No original declaration or complete value view supplied a schema.
        // Erased runtime shape cannot reconstruct missing Source coordinates.
        None
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
        let key = self.original_source_receiving_key(&value, syntax, frame);
        self.call_input_source.evaluated.insert(
            (event, role),
            Input {
                context,
                expression: Some(expression),
                allocation_epoch,
                key,
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
        let key = self.original_source_receiving_key(&value, syntax, frame);
        self.call_input_source.defaults.insert(
            (event, slot),
            Input {
                context,
                expression: None,
                allocation_epoch,
                key,
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
        // First use a fully instantiated source descriptor. Missing closed
        // witnesses fall back only to the actual complete static Type rows.
        let expected = self
            .source_type_from_syntax(syntax)
            .and_then(|witness| {
                crate::static_eval::effects::bounded_argument_key(&witness.syntax, &BTreeMap::new())
            })
            .or_else(|| {
                // Normalize the declared header before selecting its actual
                // Type leaves. An open selected record is not a closed Ty
                // witness, and cannot prevent use of its real Source receipt.
                let raw = self.original_input_header_key(syntax)?;
                let selected = self.actual_input_source_selections(info, source_event, span)?;
                select(&raw, &selected, &mut 4096, 0)
            });
        let Some(expected) = expected else {
            self.unsupported(
                span,
                "call input requires its complete formal source schema",
            );
            return false;
        };
        if source_reception::sensitive(&expected, &mut 4096) == Some(false) {
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
            self.generated_entry_source_key(slot)
                .or_else(|| self.signature_entry_source_key(slot))
                .and_then(|actual| {
                    source_reception::compatible(
                        &expected,
                        &actual,
                        Some(&Construction::Opaque),
                        &mut 4096,
                    )
                })
        } else {
            input.as_ref().and_then(|input| {
                let event =
                    source_event.and_then(|event| self.copy_call_events.get(event.0 as usize))?;
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
                match &input.key {
                    Some(actual) => source_reception::compatible(
                        &expected,
                        actual,
                        Some(&input.fresh),
                        &mut 4096,
                    ),
                    None => match (&expected, &input.fresh) {
                        (ArgumentKey::Array { length, element }, Construction::Array(items))
                            if items.is_empty()
                                && length
                                    .as_ref()
                                    .is_none_or(|length| length == "const(int:0)") =>
                        {
                            source_reception::complete(element, &mut 4096)?;
                            Some(true)
                        }
                        _ => None,
                    },
                }
            })
        };
        match answer {
            Some(true) => true,
            Some(false) => {
                self.error(
                    "E0301",
                    span,
                    "original input array or callable source schema does not fit the parameter",
                    [value.cause],
                );
                false
            }
            None => {
                self.unsupported(
                    span,
                    "call input lacks its original complete schema and actual Source observation",
                );
                false
            }
        }
    }

    fn generated_entry_source_key(&mut self, slot: usize) -> Option<ArgumentKey> {
        use crate::sema::application_effect::{EntryOrigin, InputOrigin};
        let call = self
            .copy_invocations
            .get(self.copy_invocation_stack.last()?.0 as usize)?;
        let EntryOrigin::Generated { inputs, .. } = &call.entry.origin else {
            return None;
        };
        let (observation, boundary) = match inputs.get(slot)? {
            InputOrigin::Copied {
                observation,
                boundary,
            } => (*observation, Some(*boundary)),
            InputOrigin::Observed(observation) | InputOrigin::Widened(observation) => {
                (*observation, None)
            }
            InputOrigin::Scalar(kind) => {
                return Some(ArgumentKey::Name {
                    name: match kind {
                        crate::sema::application_effect::ScalarInput::PositiveInt => "int",
                        crate::sema::application_effect::ScalarInput::ByteSuffix(_)
                        | crate::sema::application_effect::ScalarInput::BufferedBytes(_) => "bytes",
                    }
                    .into(),
                    arguments: vec![],
                });
            }
        };
        let original = self
            .application_effect
            .expressions
            .get(observation.0 as usize)?;
        let source = original.source_id?;
        let node = self.semantic_hir.expression(source)?;
        let span = original.span;
        let mut work = crate::sema::source_types::WorkLimit::new(16384);
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
        let key = if let Some(source) = stored {
            source.and_then(|source| source.map(|(schema, _)| {
                use crate::sema::source_types::{projection_receipts::ProjectionOccurrence, SourceTypesError};
                let record = self.application_effect.evaluations.get(observation.0 as usize)
                    .ok_or(SourceTypesError::MissingNode)?;
                let occurrence = ProjectionOccurrence {
                    identity: record.identity.ok_or(SourceTypesError::MissingNode)?,
                    context: record.context,
                    cause: original.value.cause,
                };
                let depth = self.source_projection_receipts().unwrap_depth(occurrence, &mut work)?;
                if depth == 1 {
                    schema.project_steps(&[ril_compiler_core::projection::TypeProjection::OptionalPayload], &mut work)?.key()
                } else {
                    schema.key()
                }
            }).transpose())
        } else {
            let mut limit = crate::sema::source_types::WorkLimit::new(4096);
            match crate::sema::source_types::declarations::construction(
                source,
                &self.semantic_hir,
                &mut limit,
            ) {
                Ok(Some(key)) => Ok(Some(key)),
                Ok(None) => {
                    let witness = original.value.source_type_witness.as_ref()?;
                    if !witness.validate_closed() {
                        return None;
                    }
                    crate::static_eval::effects::bounded_argument_key(
                        &witness.syntax,
                        &BTreeMap::new(),
                    )
                    .map(Some)
                    .ok_or(crate::sema::source_types::SourceTypesError::Unresolved)
                }
                Err(error) => Err(error),
            }
        };
        let key = self.input_graph_key(key, span)?;
        if let Some(boundary) = boundary {
            let proof = self
                .copy_boundaries
                .get(boundary.0 as usize)
                .filter(|proof| proof.id == boundary)?;
            source_reception::copy_view(key, proof.mode, &mut 4096)
        } else {
            Some(key)
        }
    }

    fn signature_entry_source_key(&self, slot: usize) -> Option<ArgumentKey> {
        let call = self
            .copy_invocations
            .get(self.copy_invocation_stack.last()?.0 as usize)?;
        if call.entry.origin != crate::sema::application_effect::EntryOrigin::SignatureProbe
            || call.source_event.is_some()
            || call.declaration_probe
        {
            return None;
        }
        let input = &call.entry.arguments.get(slot)?.1;
        crate::sema::application_effect::signature_assumption(
            input,
            call.caller_activation,
            call.entry.caller_context,
            &self.bindings,
            &mut 4096,
        )
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
        let Some(parameters) = self.public_input_source_keys(callee, syntax, frame) else {
            self.unsupported(
                syntax.span,
                "public callable input requires its original complete Source signature",
            );
            return;
        };
        let context = self.invocation_context(frame.callable_owner);
        for (slot, expected) in parameters.iter().enumerate() {
            let Some(expected) = expected else { continue };
            if source_reception::sensitive(expected, &mut 4096) == Some(false) {
                continue;
            }
            let input = self
                .call_input_source
                .supplied
                .get(&event)
                .and_then(|rows| rows.get(&slot))
                .or_else(|| self.call_input_source.defaults.get(&(event, slot)))
                .cloned();
            let answer = input.as_ref().and_then(|input| {
                if input.context != context {
                    return None;
                }
                input_compatible(expected, input)
            });
            match answer {
                Some(true) => {},
                Some(false) => self.error("E0301", syntax.span,
                    "original input source does not fit the actual public callable signature", [callee.cause]),
                None => self.unsupported(syntax.span,
                    "public callable input lost its complete original schema or actual operand identity"),
            }
        }
    }

    fn public_input_source_keys(
        &mut self,
        callee: &Value,
        syntax: &Expr,
        frame: &Frame,
    ) -> Option<Vec<Option<ArgumentKey>>> {
        // A sealed public view has priority over an underlying inferred lambda.
        if let Some(ArgumentKey::Callable { parameters, .. }) =
            self.original_source_receiving_key(callee, syntax, frame)
        {
            return Some(parameters.into_iter().map(|(_, key)| Some(key)).collect());
        }
        if callee.callables.is_empty() {
            return None;
        }
        let mut common = None;
        for callable in &callee.callables {
            let keys = match callable {
                Callable::Closure(index) => {
                    let closure = self.closures.get(*index)?.clone();
                    let contract = self.lambda_contract(*index)?.clone();
                    let previous = self.enter_typing_environment(&contract.typing_environment);
                    let keys: Option<Vec<_>> = closure
                        .parameters
                        .iter()
                        .map(|parameter| match &parameter.ty {
                            None => Some(None),
                            Some(syntax) => {
                                let target = self.freeze_source_receiving_target(syntax);
                                if target.sensitivity
                                    == source_reception::SchemaSensitivity::NotRequired
                                {
                                    Some(None)
                                } else {
                                    target.key().map(Some)
                                }
                            }
                        })
                        .collect();
                    self.restore_typing_environment(previous);
                    keys?
                }
                Callable::Symbolic(..) if self.symbolic_has_no_inputs(callee) => Vec::new(),
                _ => return None,
            };
            if common.as_ref().is_some_and(|previous| previous != &keys) {
                return None;
            }
            common = Some(keys);
        }
        common
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

fn input_compatible(expected: &ArgumentKey, input: &Input) -> Option<bool> {
    match &input.key {
        Some(actual) => {
            source_reception::compatible(expected, actual, Some(&input.fresh), &mut 4096)
        }
        None => source_reception::empty_context(expected, &input.fresh, &mut 4096),
    }
}

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
