//! Replay assignments from real source statements and frozen access receipts.
//! A structural Type constraint never supplies a mutable permission root.
use super::*;
use crate::sema::{
    bound_writes::BoundFieldWrite,
    facts::{Multiplicity, Participant, Permission},
    model::{AccessOwners, Mode},
};

impl Replay<'_> {
    pub(super) fn write_for_projection(&self, index: usize) -> Option<&BoundFieldWrite> {
        self.facts
            .bound_field_writes
            .iter()
            .find(|write| write.projection_index == index)
    }

    fn write_expression(
        &self,
        index: usize,
        context: super::super::effect_identity::InvocationContext,
        syntax: &Expr,
    ) -> Check<&Value> {
        let observation = self
            .facts
            .invocation_expressions
            .get(index)
            .filter(|observation| observation.context == context)
            .ok_or_else(|| "bounded write borrowed another invocation's expression".to_owned())?;
        let expression = self
            .facts
            .expressions
            .get(observation.expression)
            .filter(|expression| expression.span == syntax.span)
            .ok_or_else(|| "bounded write expression is not its actual source token".to_owned())?;
        Ok(&expression.value)
    }

    pub(super) fn bound_writes(&self) -> Result<(), Failure> {
        let sites = projection_sites(self.facts).map_err(|message| {
            (
                self.function_scope_span(&BoundScope::default()),
                None,
                message,
            )
        })?;
        let fallback = self.function_scope_span(&BoundScope::default());
        if self.facts.bound_field_writes.len() > LIMIT || self.facts.observed_accesses.len() > LIMIT
        {
            return Err((
                fallback,
                None,
                "bounded assignment replay budget exhausted".into(),
            ));
        }
        let mut projections = BTreeSet::new();
        let mut receipts = BTreeSet::new();
        for write in &self.facts.bound_field_writes {
            let mut check = || -> Check {
                require(
                    projections.insert(write.projection_index),
                    "bounded assignment repeats another projection's write",
                )?;
                let projection = self
                    .facts
                    .generic_bound_projections
                    .get(write.projection_index)
                    .ok_or_else(|| {
                        "bounded assignment deleted its pre-write projection".to_owned()
                    })?;
                let bound = self
                    .facts
                    .record_bounds
                    .get(projection.required.0 as usize)
                    .filter(|bound| bound.id == projection.required)
                    .ok_or_else(|| "bounded assignment has no source constraint".to_owned())?;
                let Slot::Field(label) = &projection.slot else {
                    return Err("bounded assignment requires an exact named field".into());
                };
                let field = bound
                    .fields
                    .iter()
                    .find(|field| &field.label == label)
                    .ok_or_else(|| {
                        "bounded assignment is outside its guaranteed fields".to_owned()
                    })?;
                require(
                    field.mutable
                        && projection.access == BoundAccess::ValueOnly
                        && write.span == projection.span
                        && write.cause == projection.cause,
                    "bounded assignment changed member mutability or its pre-write occurrence",
                )?;
                let owner = projection
                    .context
                    .owner
                    .ok_or_else(|| "bounded assignment has no lexical owner".to_owned())?;
                let matching: Vec<_> = sites
                    .iter()
                    .filter(|site| {
                        site.owner == owner
                            && site.expression.span == write.span
                            && site.assignment.is_some()
                    })
                    .collect();
                require(
                    matching.len() == 1,
                    "bounded assignment has no unique real source statement",
                )?;
                let site = matching[0];
                require(
                    site.supported
                        && matches!(site.expression.kind, ExprKind::Field { safe: false, .. }),
                    "bounded assignment requires its actual direct field target",
                )?;
                let (rhs, operator) = site.assignment.unwrap();
                require(
                    operator == write.operator && operator == "=",
                    "compound bounded assignment needs an independently evaluated operator witness",
                )?;
                let receiver = self.write_expression(
                    write.receiver_expression,
                    projection.context,
                    site.base,
                )?;
                let incoming =
                    self.write_expression(write.rhs_expression, projection.context, rhs)?;
                require(
                    write.rhs_expression < write.receiver_expression
                        && receiver == &projection.source.value,
                    "bounded assignment changed the RHS-before-receiver order or receiver",
                )?;
                let source = &projection.source.value;
                require(
                    source.permission == Permission::Write
                        && source.publication != Publication::Immutable
                        && source.origins.nodes.len() == 1
                        && source.sources.len() == 1,
                    "bounded assignment has no exact writable received path",
                )?;
                let origin = *source.origins.nodes.first().unwrap();
                let original_node = projection
                    .source
                    .nodes
                    .iter()
                    .find(|node| node.origin == origin)
                    .ok_or_else(|| "bounded assignment lost its real stored receiver".to_owned())?;
                require(
                    original_node.fact.multiplicity == Multiplicity::One,
                    "bounded assignment to an object family needs weak-update replay",
                )?;
                let binding_id = *source.sources.first().unwrap();
                let binding = self.facts.bindings.get(binding_id).ok_or_else(|| {
                    "bounded assignment has no genuine parameter binding".to_owned()
                })?;
                let ExprKind::Name(name) = &site.base.kind else {
                    return Err(
                        "nested mutable source requires an exact formal product-loan path".into(),
                    );
                };
                require(
                    binding.parameter
                        && binding.owner == projection.activation
                        && &binding.name == name
                        && binding.root.0 as usize == binding_id,
                    "bounded assignment borrowed another mutable parameter root",
                )?;
                let loans: Vec<_> = self
                    .facts
                    .invocation_loan_starts
                    .iter()
                    .filter(|loan| {
                        loan.owner == projection.context.owner
                            && loan.named == projection.context.invocation
                            && loan.activation == projection.activation
                            && source.participants == BTreeSet::from([Participant::Loan(loan.loan)])
                    })
                    .collect();
                require(
                    loans.len() == 1,
                    "bounded assignment has no unique actual mutable loan",
                )?;
                let loan = loans[0];
                let call = projection
                    .context
                    .invocation
                    .and_then(|id| self.facts.copy_invocations.get(id.0 as usize))
                    .filter(|call| {
                        Some(CallableOwner::Function(call.target)) == projection.context.owner
                            && call.status == CopyInvocationStatus::Completed
                    })
                    .ok_or_else(|| {
                        "bounded assignment has no complete real invocation".to_owned()
                    })?;
                let function = self.function(call.target)?;
                require(
                    call.arguments.len() == function.syntax.parameters.len(),
                    "bounded assignment invocation entry has the wrong arity",
                )?;
                let parameter = function
                    .syntax
                    .parameters
                    .get(loan.parameter as usize)
                    .ok_or_else(|| "bounded assignment loan has no real formal index".to_owned())?;
                let (mode, entry) =
                    call.arguments.get(loan.parameter as usize).ok_or_else(|| {
                        "bounded assignment lost its real whole argument entry".to_owned()
                    })?;
                // Mut reception marks a path temporary before loan creation.
                // Reconstruct that declared restriction; do not grant write
                // permission or replace the entry's origins/participants.
                let mut expected_loan_source = entry.value.clone();
                expected_loan_source.temporary = true;
                require(
                    !loan.retained
                        && parameter.mode == ril_syntax::ast::ParameterMode::Mut
                        && *mode == Mode::Write
                        && matches!(&parameter.pattern.kind, ril_syntax::ast::PatternKind::Name(actual) if actual == name)
                        && loan.bindings.contains(&binding_id)
                        && binding.forwarded == entry.value.sources
                        && loan.source == expected_loan_source
                        && loan.origins == source.origins
                        && loan.source.permission == Permission::Write
                        && loan.allocation_epoch == projection.allocation_epoch
                        && call.entry_allocation_epoch == projection.allocation_epoch,
                    "bounded assignment replaced its actual mut reception or allocation epoch",
                )?;
                let receipt = self
                    .facts
                    .observed_accesses
                    .get(write.access.0 as usize)
                    .filter(|receipt| receipt.id == write.access)
                    .ok_or_else(|| {
                        "bounded assignment has no historical access receipt".to_owned()
                    })?;
                receipts.insert(write.access);
                let access = &receipt.access;
                require(
                    receipt.context == projection.context
                        && receipt.activation == projection.activation
                        && access.observed_recency == projection.allocation_epoch
                        && access.recency == access.observed_recency
                        && access.origins == source.origins
                        && access.participants == source.participants
                        && access.mode == Mode::Write
                        && access.slot == Some(projection.slot.clone())
                        && access.cause == source.cause
                        && access.span == projection.span
                        && access
                            .origin_owners
                            .keys()
                            .copied()
                            .collect::<BTreeSet<_>>()
                            == source.origins.nodes,
                    "bounded assignment changed or normalized its historical access receipt",
                )?;
                for origin in &source.origins.nodes {
                    let node = projection
                        .source
                        .nodes
                        .iter()
                        .find(|node| node.origin == *origin)
                        .ok_or_else(|| {
                            "historical write access lost its frozen owner".to_owned()
                        })?;
                    require(
                        access.origin_owners.get(origin)
                            == Some(&AccessOwners::Known(BTreeSet::from([node.fact.owner]))),
                        "historical write access changed its original storage ownership",
                    )?;
                }
                let mut transported = access.clone();
                transported.transport(&self.facts.allocation_history);
                let summaries: Vec<_> = self
                    .facts
                    .invocations
                    .iter()
                    .filter(|summary| {
                        summary.context == Some(projection.context)
                            && summary.activation == Some(projection.activation)
                    })
                    .collect();
                require(
                    summaries.len() == 1,
                    "bounded assignment lost its actual access summary",
                )?;
                for origin in &transported.origins.nodes {
                    for participant in &transported.participants {
                        require(
                            summaries[0]
                                .accesses
                                .contains(&super::super::summary::Footprint {
                                    origin: *origin,
                                    participant: *participant,
                                    access: super::super::summary::Access::Write,
                                }),
                            "bounded assignment erased its actual exclusive-access obligation",
                        )?;
                    }
                }
                self.snapshot(&write.replacement)?;
                self.snapshot(&write.updated_receiver)?;
                let replacement = &write.replacement.value;
                require(
                    replacement == incoming
                        && replacement.ty == projection.output.value.ty
                        && replacement.ty.scalar()
                        && replacement.origins.nodes.is_empty()
                        && replacement.results.is_empty()
                        && replacement.callables.is_empty()
                        && replacement.pending_copies.is_empty(),
                    "bounded assignment replacement needs exact scalar receiving evidence",
                )?;
                self.ty_matches(&replacement.ty, &field.key, &bound.scope, 0)?;
                self.storage_shape(&write.replacement, replacement, &field.key, 0)?;
                require(
                    write.updated_receiver.value == *source
                        && write.updated_receiver.nodes.len() == projection.source.nodes.len()
                        && write.updated_receiver.relations == projection.source.relations,
                    "bounded assignment changed receiver identity or graph relations",
                )?;
                for before in &projection.source.nodes {
                    let after = write
                        .updated_receiver
                        .nodes
                        .iter()
                        .find(|node| node.origin == before.origin)
                        .ok_or_else(|| "bounded assignment removed a stored node".to_owned())?;
                    let mut fields = before.fields.clone();
                    if before.origin == origin {
                        let stored = fields
                            .iter_mut()
                            .find(|(slot, _)| slot == &projection.slot)
                            .ok_or_else(|| {
                                "bounded assignment invented a missing old field".to_owned()
                            })?;
                        stored.1 = replacement.clone();
                    }
                    require(
                        after.fact == before.fact
                            && after.fields == fields
                            && after.length == before.length
                            && after.fixed == before.fixed,
                        "bounded assignment changed another stored field, node or source shape",
                    )?;
                }
                Ok(())
            };
            check().map_err(|message| (write.span, Some(write.cause), message))?;
        }
        for (index, access) in self.facts.observed_accesses.iter().enumerate() {
            if access.id.0 as usize != index || !receipts.contains(&access.id) {
                return Err((
                    access.access.span,
                    Some(access.access.cause),
                    "historical access arena contains an invalid or unclaimed write receipt".into(),
                ));
            }
        }
        Ok(())
    }
}
