//! Validate identity metadata independently, including frozen historical values.
use super::{
    SemanticFacts,
    copy_contract::{CopyNode, CopyValueSnapshot},
    model::{CallableReturnBound, SourceTypeWitness, Value},
};
use ril_compiler_core::{diagnostic::CauseId, source::Span};
use ril_syntax::ast::{TypeDeclaration, TypeKind};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

/// The producer has already normalized aliases and substituted actual binders.
/// A remaining name must be an existing nominal declaration or builtin type,
/// never a free generic spelling accidentally treated as a closed constant.
pub(super) fn resolved_names(
    witness: &SourceTypeWitness,
    declarations: &BTreeMap<String, TypeDeclaration>,
) -> bool {
    let mut pending = vec![&witness.syntax];
    let mut visits = 0;
    while let Some(syntax) = pending.pop() {
        visits += 1;
        if visits > 4096 {
            return false;
        }
        match &syntax.kind {
            TypeKind::Name { path, arguments } => {
                let full = path.join("::");
                let name = full.strip_prefix("Prelude::").unwrap_or(&full);
                let known = matches!(
                    name,
                    "bool"
                        | "str"
                        | "bytes"
                        | "never"
                        | "f32"
                        | "f64"
                        | "int"
                        | "i8"
                        | "i16"
                        | "i32"
                        | "i64"
                        | "i128"
                        | "isize"
                        | "u8"
                        | "u16"
                        | "u32"
                        | "u64"
                        | "u128"
                        | "usize"
                        | "bigint"
                        | "Immut"
                        | "Option"
                        | "Result"
                        | "Set"
                        | "Range"
                        | "Heap::Heap"
                        | "Deque::Deque"
                ) || (arguments.is_empty()
                    && super::checker::is_known_builtin_source_type(&full))
                    || declarations.get(&full).is_some_and(|declaration| {
                        declaration.nominal
                            || declaration.opaque
                            || !declaration.variants.is_empty()
                    });
                if !known {
                    return false;
                }
                pending.extend(arguments);
            }
            TypeKind::Optional(inner) | TypeKind::Array { element: inner, .. } => {
                pending.push(inner)
            }
            TypeKind::Map { key, value } => pending.extend([&**key, &**value]),
            TypeKind::Tuple(items) => pending.extend(items),
            TypeKind::Record { fields, .. } => pending.extend(fields.iter().map(|field| &field.ty)),
            TypeKind::Callable {
                parameters, result, ..
            } => {
                pending.extend(
                    parameters
                        .iter()
                        .filter_map(|parameter| parameter.ty.as_ref()),
                );
                pending.extend(result.iter().map(|result| &**result));
            }
            TypeKind::Computation(_) => {}
            _ => return false,
        }
    }
    true
}

pub(super) fn validate(facts: &SemanticFacts) -> Result<(), (Span, CauseId)> {
    struct Walk<'a> {
        facts: &'a SemanticFacts,
        pending: Vec<&'a Value>,
        witnesses: BTreeSet<usize>,
        contracts: BTreeSet<usize>,
        environments: BTreeSet<super::context::FrozenEnvId>,
    }
    impl<'a> Walk<'a> {
        fn nodes(&mut self, nodes: &'a [CopyNode]) {
            self.pending.extend(
                nodes
                    .iter()
                    .flat_map(|node| node.fields.iter().map(|(_, value)| value)),
            );
        }
        fn snapshot(&mut self, snapshot: &'a CopyValueSnapshot) {
            self.pending.push(&snapshot.value);
            self.nodes(&snapshot.nodes);
        }
        fn witness(&mut self, witness: &Arc<SourceTypeWitness>) -> bool {
            !self.witnesses.insert(Arc::as_ptr(witness) as usize)
                || witness.validate_closed()
                    && resolved_names(witness, &self.facts.external_type_declarations)
        }
        fn environment(&mut self, environment: &super::context::FrozenEnvironment) -> bool {
            if environment.is_poisoned() {
                return false;
            }
            if !self.environments.insert(environment.id()) {
                return true;
            }
            self.environments.len() <= 65536
                && environment
                    .contract_bindings
                    .values()
                    .all(|id| *id < self.facts.bindings.len())
                && environment
                    .generic_type_witnesses
                    .values()
                    .all(|witness| self.witness(witness))
                && environment
                    .bound_row_selections
                    .values()
                    .filter_map(|selection| selection.source_type_witness.as_ref())
                    .all(|witness| self.witness(witness))
        }
        fn contract(&mut self, head: &Arc<CallableReturnBound>) -> bool {
            let mut pending = vec![head];
            while let Some(bound) = pending.pop() {
                if !self.contracts.insert(Arc::as_ptr(bound) as usize) {
                    continue;
                }
                if self.contracts.len() > 65536 || !self.environment(&bound.typing_environment) {
                    return false;
                }
                pending.extend(&bound.predecessors);
            }
            true
        }

        fn callable_bound(&mut self, bound: &super::model::CallableBound) -> bool {
            use crate::hir::nodes::{ExprKind, TypeKind};
            use ril_compiler_core::ids::CallableContractSource;
            if !self.environment(&bound.typing_environment) {
                return false;
            }
            let Some(source) = bound.source else {
                return true;
            };
            let Some(hir) = self.facts.semantic_hir.as_deref() else {
                return false;
            };
            let original = match source {
                CallableContractSource::Type(id) => {
                    match hir.type_expression(id).map(|node| &node.kind) {
                        Some(TypeKind::Callable { annotations, .. }) => annotations,
                        _ => return false,
                    }
                }
                CallableContractSource::Expression(id) => {
                    match hir.expression(id).map(|node| &node.kind) {
                        Some(ExprKind::Lambda { annotations, .. }) => annotations,
                        _ => return false,
                    }
                }
            };
            original.len() == bound.annotations.len()
                && original
                    .iter()
                    .zip(&bound.annotations)
                    .all(|(original, captured)| {
                        original.kind == captured.kind && original.text == captured.text
                    })
        }
    }
    let mut walk = Walk {
        facts,
        pending: vec![],
        witnesses: BTreeSet::new(),
        contracts: BTreeSet::new(),
        environments: BTreeSet::new(),
    };
    walk.pending.extend(facts.fields.values());
    walk.pending
        .extend(facts.bindings.iter().map(|binding| &binding.value));
    walk.pending
        .extend(facts.expressions.iter().map(|expression| &expression.value));
    walk.pending
        .extend(facts.constant_values.iter().map(|constant| &constant.value));
    walk.pending
        .extend(facts.invocation_loan_starts.iter().map(|loan| &loan.source));
    for binding in &facts.bindings {
        if !walk.environment(&binding.typing_environment) {
            return Err((binding.span, binding.value.cause));
        }
    }
    for handler in &facts.handlers {
        if handler.lexical != handler.typing_environment.contract_bindings
            || !walk.environment(&handler.typing_environment)
        {
            return Err((handler.span, CauseId(0)));
        }
    }
    for function in &facts.functions {
        if function.lexical != function.typing_environment.contract_bindings
            || !walk.environment(&function.typing_environment)
        {
            return Err((function.syntax.span, CauseId(0)));
        }
    }
    for closure in &facts.closures {
        if closure.lexical != closure.contract.typing_environment.contract_bindings
            || !walk.environment(&closure.contract.typing_environment)
        {
            return Err((closure.contract.span, CauseId(0)));
        }
    }
    for check in &facts.generic_bound_checks {
        walk.snapshot(&check.actual);
        if let super::record_bounds::StructuralSchemaSource::Closed(witness) =
            &check.actual_schema.source
            && !walk.witness(witness)
        {
            return Err((check.span, check.cause));
        }
        for selection in &check.rows {
            if let Some(witness) = &selection.source_type_witness
                && !walk.witness(witness)
            {
                return Err((check.span, check.cause));
            }
        }
    }
    for projection in &facts.generic_bound_projections {
        walk.snapshot(&projection.source);
        walk.snapshot(&projection.output);
    }
    for discard in &facts.closure_discards {
        walk.snapshot(&discard.value);
    }
    for usage in &facts.default_uses {
        if let Some(result) = &usage.result {
            walk.snapshot(result);
        }
    }
    for boundary in &facts.copy_boundaries {
        walk.pending.push(&boundary.source);
        walk.pending.extend(boundary.output.as_ref());
        walk.pending.extend(
            boundary
                .constituents
                .iter()
                .filter_map(|constituent| constituent.source.as_ref()),
        );
        walk.nodes(&boundary.nodes);
        walk.nodes(&boundary.output_nodes);
    }
    for invocation in &facts.copy_invocations {
        for (_, argument) in &invocation.entry.arguments {
            walk.snapshot(argument);
        }
        if let Some(result) = &invocation.result {
            walk.snapshot(result);
        }
    }
    for event in &facts.resource_clones {
        walk.snapshot(&event.source);
        walk.snapshot(&event.output);
        walk.nodes(&event.anchors);
    }
    for loan in &facts.operation_loan_starts {
        walk.snapshot(&loan.source);
    }
    for event in &facts.channel_messages {
        use super::channel_messages::ChannelAction;
        match &event.action {
            ChannelAction::Send {
                endpoint,
                payload,
                transport,
                ..
            }
            | ChannelAction::Receive {
                endpoint,
                payload,
                transport,
                ..
            } => {
                walk.snapshot(endpoint);
                walk.snapshot(payload);
                walk.snapshot(transport);
            }
            ChannelAction::TagTest { subject, .. }
            | ChannelAction::ConditionEvaluated { subject, .. } => walk.snapshot(subject),
            ChannelAction::Inspect { value, .. } => walk.snapshot(value),
            ChannelAction::ResultTransfer { source, .. } => walk.snapshot(source),
            ChannelAction::Select { .. }
            | ChannelAction::ResultAliases { .. }
            | ChannelAction::TaskFork { .. }
            | ChannelAction::TaskJoin { .. } => {}
        }
    }
    for exit in &facts.channel_exits {
        walk.snapshot(&exit.returned);
    }
    for step in &facts.resumption_steps {
        walk.snapshot(&step.continuation_value);
        walk.snapshot(&step.arm_value);
        if let Some(exit) = &step.scope_exit {
            walk.snapshot(&exit.answer_before);
            walk.snapshot(&exit.answer_received);
            walk.pending
                .extend(exit.bindings.iter().map(|binding| &binding.value));
            walk.nodes(&exit.nodes);
        }
    }
    let mut visits = 0usize;
    while let Some(value) = walk.pending.pop() {
        visits += 1;
        if visits > 1_000_000
            || value
                .source_type_witness
                .as_ref()
                .is_some_and(|witness| !walk.witness(witness))
            || value
                .callable_returns
                .iter()
                .any(|bound| !walk.contract(bound))
            || value
                .callable_bounds
                .iter()
                .any(|bound| !walk.callable_bound(bound))
        {
            return Err((
                value.source_type_witness.as_ref().map_or(
                    Span {
                        file: facts.file.unwrap_or(ril_compiler_core::source::FileId(0)),
                        start: 0,
                        end: 0,
                    },
                    |witness| witness.syntax.span,
                ),
                value.cause,
            ));
        }
        walk.pending.extend(
            [
                &value.option_payload,
                &value.result_payload,
                &value.result_success,
                &value.result_error,
                &value.variant_payload,
            ]
            .into_iter()
            .flatten()
            .map(Box::as_ref),
        );
        walk.pending
            .extend(value.variant_witnesses.values().map(Box::as_ref));
    }
    Ok(())
}
