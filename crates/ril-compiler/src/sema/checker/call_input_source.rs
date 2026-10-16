//! Original input schemas, before any receiving ascription. Stored array
//! cardinality is deliberately absent; only a real literal AST supplies fresh
//! receiving context. This private state is replayed through CallArguments.
use super::*;
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

pub(super) struct Callee<'a> {
    pub value: &'a Value,
    pub syntax: &'a Expr,
}

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
    supplied: BTreeMap<CopyCallEventId, BTreeMap<usize, Input>>,
    defaults: BTreeMap<(CopyCallEventId, usize), Input>,
    operands: Vec<Operand>,
    carriers: BTreeMap<u32, (CopyCallEventId, InvocationContext)>,
    carrier_sources: BTreeMap<u32, ArgumentKey>,
    local_views: BTreeMap<BindingId, Option<ArgumentKey>>,
    closure_views: BTreeMap<usize, (u32, ArgumentKey)>,
}

struct Operand {
    syntax: usize,
    span: Span,
    context: InvocationContext,
    event: CopyCallEventId,
    slot: u32,
}

impl Checker {
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
            .filter_map(|parameter| self.generic_context.get(&parameter.name).cloned())
            .collect();
        for binder in &owned {
            self.generic_substitutions.remove(binder);
            self.generic_type_witnesses.remove(binder);
            self.static_key_arguments.remove(binder);
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
                    owned.contains(name) && !self.generic_substitutions.contains_key(name)
                }) {
                    return None;
                }
                let target = self.freeze_source_receiving_target(syntax);
                target.key.as_ref()?;
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
            syntax: std::ptr::from_ref(syntax) as usize,
            span: syntax.span,
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
        (operand.syntax == std::ptr::from_ref(syntax) as usize
            && operand.span == syntax.span
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
        let unwrap = self.invocation_witnesses.iter().filter(|row| {
            row.context == context && row.span == syntax.span
                && matches!(&row.kind, crate::sema::effect_identity::InvocationWitnessKind::ImplicitUnwrap(proof)
                    if proof.cause == value.cause && proof.depth == 1 && proof.tags == ["Some"])
        }).count() == 1;
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
        if let Some(key) = self.storage_binding_source_key(value, syntax, frame) {
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
        if let ExprKind::Name(name) = &syntax.kind
            && value.sources.len() == 1
            && let Some(id) = value.sources.first()
            && self
                .bindings
                .get(*id)
                .is_some_and(|binding| binding.name == *name)
            && let Some(view) = self.call_input_source.local_views.get(id)
        {
            return view.clone();
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
            if binding.parameter && binding.owner == frame.owner {
                if matches!(frame.callable_owner, Some(CallableOwner::Lambda(_))) {
                    return self.formal_source_type_key(value, syntax, frame);
                }
                let function = self.functions.iter().find(|function| {
                    frame.callable_owner == Some(CallableOwner::Function(function.definition))
                })?;
                let parameter = function.syntax.parameters.iter().find(|parameter|
                    parameter.pattern.span == binding.span && matches!(&parameter.pattern.kind, PatternKind::Name(actual) if actual == name))?;
                let ty = parameter.ty.clone()?;
                return self.freeze_source_receiving_target(&ty).key;
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
        let syntax = io_types::receiver_type(value, &value.ty, syntax.span)?;
        crate::static_eval::effects::bounded_argument_key(&syntax, &self.effect_type_binders)
    }

    pub(super) fn record_call_input_source(
        &mut self,
        event: CopyCallEventId,
        slot: usize,
        syntax: &Expr,
        observed: Option<usize>,
        frame: &Frame,
    ) {
        let Some(expression) = observed else {
            return;
        };
        let Some(observation) = self.expression_facts.get(expression) else {
            return;
        };
        let context = self.invocation_context(frame.callable_owner);
        if observation.span != syntax.span
            || !self
                .invocation_expressions
                .get(expression)
                .is_some_and(|row| {
                    row.expression == expression
                        && row.context == context
                        && row.argument_of == Some((event, slot as u32))
                })
        {
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
        let allocation_epoch = self.recency_moves.len();
        let key = self.original_source_receiving_key(&value, syntax, frame);
        self.call_input_source
            .supplied
            .entry(event)
            .or_default()
            .insert(
                slot,
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
        let answer = input.as_ref().and_then(|input| {
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
                            && self
                                .copy_invocations
                                .get(id.0 as usize)
                                .is_some_and(|call| {
                                    call.source_event == Some(event.id)
                                        && call.target == info.definition
                                }) => {}
                    _ => return None,
                }
            } else if event.owner != input.context.owner || event.parent != input.context.invocation
            {
                return None;
            }
            match &input.key {
                Some(actual) => {
                    source_reception::compatible(&expected, actual, Some(&input.fresh), &mut 4096)
                }
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
        });
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
                    let contract = self.lambda_contracts.get(index)?.clone();
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
                                    target.key.map(Some)
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
        None => match (expected, &input.fresh) {
            (ArgumentKey::Array { length, element }, Construction::Array(items))
                if items.is_empty() =>
            {
                source_reception::complete(element, &mut 4096)?;
                Some(
                    length
                        .as_ref()
                        .is_none_or(|length| length == "const(int:0)"),
                )
            }
            _ => None,
        },
    }
}

fn select(
    key: &ArgumentKey,
    selected: &BTreeMap<String, ArgumentKey>,
    work: &mut usize,
    depth: usize,
) -> Option<ArgumentKey> {
    *work = work.checked_sub(1)?;
    if depth > 64 {
        return None;
    }
    let mut child = |key| select(key, selected, work, depth + 1);
    Some(match key {
        ArgumentKey::Binder { identity, .. } => match selected.get(identity) {
            Some(value) if value != key => child(value)?,
            _ => key.clone(),
        },
        ArgumentKey::Array { length, element } => ArgumentKey::Array {
            length: length.clone(),
            element: Box::new(child(element)?),
        },
        ArgumentKey::Map { key, value } => ArgumentKey::Map {
            key: Box::new(child(key)?),
            value: Box::new(child(value)?),
        },
        ArgumentKey::Name { name, arguments } => ArgumentKey::Name {
            name: name.clone(),
            arguments: arguments.iter().map(&mut child).collect::<Option<_>>()?,
        },
        ArgumentKey::Tuple(items) => {
            ArgumentKey::Tuple(items.iter().map(&mut child).collect::<Option<_>>()?)
        }
        ArgumentKey::Record { fields, row } => {
            let mut fields: Vec<_> = fields
                .iter()
                .map(|(name, mutable, value)| Some((name.clone(), *mutable, child(value)?)))
                .collect::<Option<_>>()?;
            let mut row = match row {
                Some(row) => Some(Box::new(child(row)?)),
                None => None,
            };
            if let Some(tail) = row.take() {
                match *tail {
                    ArgumentKey::Record {
                        fields: extra,
                        row: rest,
                    } => {
                        for field in extra {
                            if fields.iter().any(|old| old.0 == field.0) {
                                return None;
                            }
                            fields.push(field);
                        }
                        row = rest;
                    }
                    other => row = Some(Box::new(other)),
                }
            }
            fields.sort_by(|left, right| left.0.cmp(&right.0));
            ArgumentKey::Record { fields, row }
        }
        ArgumentKey::Callable {
            parameters,
            result,
            annotations,
        } => ArgumentKey::Callable {
            parameters: parameters
                .iter()
                .map(|(mode, value)| Some((*mode, child(value)?)))
                .collect::<Option<_>>()?,
            result: Box::new(child(result)?),
            annotations: annotations.clone(),
        },
        _ => key.clone(),
    })
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
        let expressions: Vec<_> = checker.invocation_expressions.iter().filter_map(|row| {
            let fact = checker.expression_facts.get(row.expression)?;
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
