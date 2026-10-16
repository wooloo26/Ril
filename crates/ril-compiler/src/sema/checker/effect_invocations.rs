//! Exact invocation partitions accompany global summary maps. An event is an
//! observation, not permission to specialize a missing or conflicting path.
use super::super::effect_identity::{InvocationContext, InvocationWitness, InvocationWitnessKind};
use super::*;

impl Checker {
    pub(super) fn invocation_context(&self, owner: Option<CallableOwner>) -> InvocationContext {
        InvocationContext {
            invocation: self.copy_invocation_stack.last().copied(),
            owner,
            closure: self
                .closure_invocation_stack
                .last()
                .map(|id| self.closure_invocations[id.0 as usize].closure),
            closure_invocation: self.closure_invocation_stack.last().copied(),
            budget_validation: self.budget_validation_depth > 0,
            default_use: self.default_use_stack.last().copied(),
        }
    }

    pub(super) fn invocation_witness(
        &mut self,
        owner: Option<CallableOwner>,
        span: Span,
        kind: InvocationWitnessKind,
    ) {
        self.invocation_witnesses.push(InvocationWitness {
            context: self.invocation_context(owner),
            span,
            kind,
        });
    }

    pub(super) fn expression_witness(&mut self, span: Span, kind: InvocationWitnessKind) {
        let owner = self.expression_owners.last().copied().flatten();
        self.invocation_witness(owner, span, kind);
    }

    pub(super) fn record_variant_projection(
        &mut self,
        owner: Option<CallableOwner>,
        span: Span,
        proof: super::super::VariantProjection,
    ) {
        self.invocation_witness(
            owner,
            span,
            InvocationWitnessKind::VariantProjection(proof.clone()),
        );
        self.variant_projections
            .insert((span.file.0, span.start, span.end), proof);
    }
}
