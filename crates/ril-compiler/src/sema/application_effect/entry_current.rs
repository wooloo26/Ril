//! Current value recipes consume authenticated physical packets. None of the
//! retained recipe fields certifies its own input, projection or Source.
use super::*;
use crate::hir::nodes::{ExprKind, HirProgram};
use crate::sema::{
    copy_contract::CopyCallEventId,
    default_uses::EvaluationRole,
    evaluated::{
        CurrentValueStep, SourceRef, catalog_callable_bound, projected_value, read_handle,
    },
    facts::{CauseKind, Slot},
    model::Callable,
    source_types::{
        SourcePath,
        projection_receipts::{ProjectionOccurrence, ProjectionReceipts},
    },
    source_types_ref::SourceTypesRef,
};
use ril_compiler_core::{diagnostic::CauseId, ids::ExprId};
use std::sync::Arc;

fn field_source(
    hir: &HirProgram,
    receiver: ExprId,
    slot: &Slot,
    work: &mut usize,
) -> Check<ExprId> {
    charge(work, 1)?;
    match slot {
        Slot::Field(name) => {
            crate::sema::application_effect::record_field_source(hir, receiver, name, work)
                .ok_or_else(|| "current projection has no original record field".into())
        }
        Slot::Tuple(index) => {
            let Some(node) = hir.expression(receiver) else {
                return Err("current tuple projection lost its HIR".into());
            };
            let ExprKind::Tuple(items) = &node.kind else {
                return Err("current tuple projection is not a tuple construction".into());
            };
            items
                .get(*index as usize)
                .copied()
                .ok_or_else(|| "current tuple projection has no original child".into())
        }
        _ => Err("current projection lacks a supported original constituent role".into()),
    }
}

fn operand_source(
    hir: &HirProgram,
    source: ExprId,
    role: EvaluationRole,
    work: &mut usize,
) -> Check<ExprId> {
    charge(work, 2)?;
    let node = hir
        .expression(source)
        .ok_or("current projection lost its original application")?;
    let (piped, callee, arguments) = match &node.kind {
        ExprKind::Call { callee, arguments } => (None, *callee, arguments.as_slice()),
        ExprKind::Binary {
            operator,
            left,
            right,
        } => {
            charge(work, 1 + operator.len().div_ceil(32))?;
            require(
                matches!(operator.as_str(), "|>" | "!>"),
                "current projection is not an original application",
            )?;
            match &hir
                .expression(*right)
                .ok_or("current pipeline lost its right operand")?
                .kind
            {
                ExprKind::Call { callee, arguments } => {
                    (Some(*left), *callee, arguments.as_slice())
                }
                _ => (Some(*left), *right, &[][..]),
            }
        }
        _ => return Err("current projection has no original application role".into()),
    };
    match role {
        EvaluationRole::Callee => Ok(callee),
        EvaluationRole::Piped => {
            piped.ok_or_else(|| "current projection borrowed a piped operand".into())
        }
        EvaluationRole::Written(index) => arguments
            .get(index as usize)
            .map(|argument| argument.value)
            .ok_or_else(|| "current projection borrowed a written operand".into()),
    }
}

impl Replay<'_> {
    fn current_input(&mut self, packet: &EvaluatedValue, depth: usize, work: &mut usize) -> Check {
        charge(work, 1)?;
        let observation = packet
            .birth_coordinates()
            .observation
            .ok_or("current recipe input has no actual physical birth")?;
        self.physical_depth(
            packet,
            observation,
            PhysicalPosition {
                epoch: packet.current_epoch(),
                current: true,
                depth: depth + 1,
                purpose: PhysicalPurpose::Receiver,
            },
            work,
        )
    }

    /// The receiver is an actual supplied operand, not a record recovered from
    /// the final heap. Slot binding and physical ordering remain independent.
    fn projection_argument(
        &self,
        receiver: &EvaluatedValue,
        work: &mut usize,
    ) -> Check<(CopyCallEventId, u32)> {
        charge(work, 5)?;
        let facts = self.facts;
        let observation = receiver
            .birth_coordinates()
            .observation
            .ok_or("current projection receiver lost its birth")?;
        let record = facts
            .evaluations
            .get(observation)
            .ok_or("current projection receiver has no record")?;
        let pairing = facts
            .invocation_expressions
            .get(observation)
            .ok_or("current projection receiver lost its application pairing")?;
        let (event_id, slot) = pairing
            .argument_of
            .ok_or("current projection receiver was not an actual supplied operand")?;
        require(
            pairing.expression == observation && pairing.context == record.context,
            "current projection receiver borrowed another application pairing",
        )?;
        let event = facts
            .copy_call_events
            .get(event_id.0 as usize)
            .filter(|event| event.id == event_id)
            .ok_or("current projection receiver lost its actual application")?;
        charge(
            work,
            2 + self.preparations.len().checked_ilog2().unwrap_or(0) as usize,
        )?;
        let preparation = self
            .preparations
            .get(&event_id)
            .copied()
            .ok_or("current projection lost its original preparation")?;
        charge(
            work,
            2 + preparation.supplied.len().checked_ilog2().unwrap_or(0) as usize,
        )?;
        require(
            preparation.slots_bound
                && preparation.evaluation_complete
                && preparation.slots.get(slot as usize) == Some(&ArgumentSource::Supplied)
                && preparation.supplied.get(&slot).is_some_and(|token| {
                    token.expression == observation
                        && token.allocation_epoch == record.allocation_epoch
                })
                && event.owner == record.context.owner
                && event.parent == record.context.invocation,
            "current projection borrowed another actual argument slot",
        )?;
        let root = event
            .result_expression
            .and_then(|index| facts.evaluations.get(index))
            .ok_or("current projection application has no physical root")?;
        let root_identity = root
            .identity
            .ok_or("current projection application lost its HIR")?;
        let entered = facts
            .activations
            .get(root_identity.activation.0 as usize)
            .ok_or("current projection application lost its activation")?;
        let receiver_identity = record
            .identity
            .ok_or("current projection receiver lost its HIR")?;
        let receiver_activation = facts
            .activations
            .get(receiver_identity.activation.0 as usize)
            .ok_or("current projection receiver lost its activation")?;
        require(
            event.source_id == Some(root_identity.source)
                && entered.id == root_identity.activation
                && entered.result == Some(root.id)
                && entered.kind == ActivationKind::Expression
                && entered.context == record.context
                && root.context == record.context
                && receiver_activation.parent == Some(entered.id)
                && record.id.0 < root.id.0,
            "current projection receiver is not in its actual application subtree",
        )?;
        charge(work, preparation.evaluated.len())?;
        let mut roles = preparation
            .evaluated
            .iter()
            .filter(|evaluation| evaluation.observation.expression == observation);
        let role = roles
            .next()
            .ok_or("current projection receiver lost its physical evaluation role")?;
        require(
            roles.next().is_none() && role.role != EvaluationRole::Callee,
            "current projection receiver has ambiguous physical roles",
        )?;
        let hir = facts
            .semantic_hir
            .as_deref()
            .ok_or("current projection has no canonical HIR")?;
        require(
            operand_source(hir, root_identity.source, role.role, work)? == receiver_identity.source,
            "current projection borrowed another original operand",
        )?;
        Ok((event_id, slot))
    }

    fn field_projection(
        &mut self,
        input: &EvaluatedValue,
        receiver: &EvaluatedValue,
        slot: &Slot,
        cause: CauseId,
        depth: usize,
        work: &mut usize,
    ) -> Check {
        charge(work, 4)?;
        self.current_input(receiver, depth, work)?;
        require(
            receiver.current_epoch() == input.current_epoch(),
            "current projection mixed input and receiver epochs",
        )?;
        self.projection_argument(receiver, work)?;
        let facts = self.facts;
        let child = input.birth_coordinates();
        let parent = receiver.birth_coordinates();
        let parent_identity = parent
            .identity
            .ok_or("current projection receiver has no actual HIR")?;
        let child_identity = child
            .identity
            .ok_or("current projection child has no actual HIR")?;
        let parent_observation = parent
            .observation
            .ok_or("current projection receiver has no actual observation")?;
        let parent_fact = facts
            .expressions
            .get(parent_observation)
            .ok_or("current projection receiver has no original value")?;
        let hir = facts
            .semantic_hir
            .as_deref()
            .ok_or("current projection has no canonical HIR")?;
        require(
            field_source(hir, parent_identity.source, slot, work)? == child_identity.source,
            "current projection changed its original field child",
        )?;
        let actual = graph(work, |budget| {
            ProjectionReceipts::from_facts(facts).child_observation(
                ProjectionOccurrence {
                    identity: parent_identity,
                    context: parent.context.ok_or(SourceTypesError::MissingNode)?,
                    cause: parent_fact.value.cause,
                },
                child_identity.source,
                budget,
            )
        })?;
        require(
            child.observation == Some(actual.0 as usize),
            "current projection borrowed another field occurrence",
        )?;
        let projection = facts
            .explanations
            .causes
            .get(cause.0 as usize)
            .ok_or("current projection lost its cause")?;
        charge(work, projection.parents.len() + 1)?;
        require(
            projection.id == cause
                && facts.explanations.kinds.get(cause.0 as usize) == Some(&CauseKind::Projection)
                && projection.parents == [receiver.value().cause, input.value().cause],
            "current projection lost its receiver and stored-child explanation",
        )
    }

    fn catalog_step(
        &mut self,
        input: &EvaluatedValue,
        event_id: CopyCallEventId,
        argument: u32,
        field: &Slot,
        depth: usize,
        work: &mut usize,
    ) -> Check {
        charge(work, 3)?;
        let CurrentSourceView::Derived {
            input: child,
            step: CurrentValueStep::FieldProjection { receiver, slot, .. },
            ..
        } = input.evidence_view().current
        else {
            return Err("catalog callable contract has no actual field projection".into());
        };
        charge(work, slot_text(slot).max(slot_text(field)))?;
        require(
            slot == field && child.shares_birth(input),
            "catalog callable contract changed its projected field",
        )?;
        require(
            self.projection_argument(receiver, work)? == (event_id, argument),
            "catalog callable contract borrowed another application or slot",
        )?;
        let facts = self.facts;
        let event = facts
            .copy_call_events
            .get(event_id.0 as usize)
            .filter(|event| event.id == event_id)
            .ok_or("catalog callable contract lost its actual primitive")?;
        let observation = event
            .callee_expression
            .ok_or("catalog callable contract lost its actual callee")?;
        let callee = facts
            .expressions
            .get(observation)
            .ok_or("catalog callable contract callee is absent")?
            .value
            .packet();
        self.current_input(callee, depth, work)?;
        let [Callable::Builtin(name)] = callee.value().callables.as_slice() else {
            return Err("catalog callable contract is not an original builtin".into());
        };
        charge(work, 1 + name.len().div_ceil(32))?;
        let contract = crate::sema::application_effect::record_callback(name)
            .ok_or("catalog callable contract has no original declaration recipe")?;
        charge(work, slot_text(field))?;
        require(
            argument == contract.operations
                && matches!(field, Slot::Field(label) if label == contract.field),
            "catalog callable contract differs from its original builtin role",
        )?;
        let original = self
            .sources(work)?
            .primitive_read(observation, name, work)?;
        // These stream primitives currently retain their universal descriptor.
        // Their fixed invocation constraint comes from the authenticated
        // primitive declaration; it does not instantiate receiver data.
        charge(work, 3 + name.len())?;
        let mut descriptor = Value::scalar(
            crate::sema::model::Ty::Unknown,
            None,
            original.declaration.cause,
        );
        descriptor.callables.push(Callable::Builtin(name.clone()));
        require(
            crate::sema::evaluated::same_birth_value(&descriptor, original.declaration, work)
                .map_err(|error| error.to_string())?,
            "catalog callable contract changed the original universal primitive descriptor",
        )?;
        require(
            crate::sema::evaluated::same_birth_value(&original.value, callee.value(), work)
                .map_err(|error| error.to_string())?,
            "catalog callable contract changed its complete historical primitive read",
        )
    }

    pub(super) fn current_derivation(
        &mut self,
        packet: &EvaluatedValue,
        input: &Arc<EvaluatedValue>,
        step: &CurrentValueStep,
        source: SourceRef,
        depth: usize,
        work: &mut usize,
    ) -> Check {
        charge(work, 3)?;
        require(
            input.shares_birth(packet) && input.current_epoch() <= packet.current_epoch(),
            "current derivation changed its original input or epoch",
        )?;
        self.current_input(input, depth, work)?;
        let mut expected =
            crate::sema::evaluated::transport_value_at(input.value(), &[], 0, 0, work)
                .map_err(|error| error.to_string())?;
        let mut expected_source = graph(work, |budget| {
            input.current_source(SourceTypesRef::Frozen(&self.facts.source_types), budget)
        })?;
        match step {
            CurrentValueStep::ReadHandle => read_handle(&mut expected),
            CurrentValueStep::FieldProjection {
                receiver,
                slot,
                cause,
            } => {
                self.field_projection(input, receiver, slot, *cause, depth, work)?;
                expected = projected_value(input.value(), receiver.value(), slot, *cause, work)
                    .map_err(|error| error.to_string())?;
                let receiver_source = graph(work, |budget| {
                    receiver
                        .current_source(SourceTypesRef::Frozen(&self.facts.source_types), budget)
                })?;
                let receiver_schema = receiver_source
                    .schema
                    .ok_or("current projection receiver has unknown Source")?;
                let projected = graph(work, |budget| {
                    let path = match slot {
                        Slot::Field(label) => {
                            budget.text(label)?;
                            SourcePath::Field(label.clone())
                        }
                        Slot::Tuple(index) => SourcePath::Tuple(*index),
                        _ => return Err(SourceTypesError::MissingProjection),
                    };
                    receiver_schema.project_steps(&[path], budget)
                })?;
                let child_source = expected_source
                    .schema
                    .as_ref()
                    .ok_or("current projection child has unknown Source")?;
                require(
                    graph(work, |budget| {
                        projected.equivalent_in(
                            child_source,
                            &receiver_source.environment,
                            &expected_source.environment,
                            budget,
                        )
                    })?,
                    "current projection changed its actual child Source",
                )?;
                if graph(work, |budget| projected.requires_environment(budget))? {
                    require(
                        expected_source.environment.id() == receiver_source.environment.id(),
                        "current projection reinterpreted its child in another environment",
                    )?;
                }
                // projected_value retains the receiver's declared child view.
                // Source equivalence does not authorize replacing that view
                // with a recursively expanded runtime representation.
                expected_source.schema = Some(projected);
                expected_source.environment = receiver_source.environment;
            }
            CurrentValueStep::CatalogCallableBound {
                event,
                argument,
                field,
                span,
            } => {
                self.catalog_step(input, *event, *argument, field, depth, work)?;
                charge(work, expected.callable_bounds.len() + 4)?;
                expected.callable_bounds.push(catalog_callable_bound(*span));
            }
        }
        let expected_schema = expected_source
            .schema
            .ok_or("current derivation has unknown input Source")?;
        let (actual_schema, actual_environment) = graph(work, |budget| {
            self.facts
                .source_types
                .view_schema(source.view, source.original, budget)
        })?;
        require(
            source.original == expected_schema.original()
                && actual_environment.id() == expected_source.environment.id()
                && graph(work, |budget| {
                    actual_schema.equivalent_in(
                        &expected_schema,
                        &actual_environment,
                        &expected_source.environment,
                        budget,
                    )
                })?,
            "current derivation changed its authentic Source or frozen interpretation",
        )?;
        let expected = crate::sema::evaluated::transport_value_at(
            &expected,
            &self.facts.allocation_history,
            input.current_epoch(),
            packet.current_epoch(),
            work,
        )
        .map_err(|error| error.to_string())?;
        if !crate::sema::evaluated::same_birth_value(&expected, packet.value(), work)
            .map_err(|error| error.to_string())?
        {
            let field = crate::sema::evaluated::value_difference(&expected, packet.value(), work)
                .map_err(|error| error.to_string())?;
            return Err(format!(
                "current derivation changed its complete projected value or duties: {field}"
            ));
        }
        Ok(())
    }
}

fn slot_text(slot: &Slot) -> usize {
    match slot {
        Slot::Field(label) => 1 + label.len().div_ceil(32),
        _ => 1,
    }
}
