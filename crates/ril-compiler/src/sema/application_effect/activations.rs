//! Enter-time evaluation identities, independent of postorder value emissions.
use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActivationKind {
    Expression,
    /// A control request. Offered operands keep their own observations;
    /// a suspended expression's completed value is recorded separately.
    ControlTransfer,
    /// An explicit numeric/transport/publication observation, rather than
    /// another execution of a syntax subtree.
    Emission,
}

#[derive(Debug, Clone)]
pub struct EvaluationActivation {
    pub id: ActivationEpochId,
    pub parent: Option<ActivationEpochId>,
    pub kind: ActivationKind,
    pub source: Option<ExprId>,
    pub scope: ScopeId,
    pub context: InvocationContext,
    pub start_expression: usize,
    pub end_expression: Option<usize>,
    pub result: Option<EvaluationOccurrenceId>,
}

impl ApplicationEffectDomain {
    pub(crate) fn enter(
        &mut self,
        source: Option<ExprId>,
        scope: ScopeId,
        context: InvocationContext,
    ) -> Option<ActivationEpochId> {
        self.enter_kind(source, scope, context, ActivationKind::Expression)
    }
    pub(crate) fn enter_kind(
        &mut self,
        source: Option<ExprId>,
        scope: ScopeId,
        context: InvocationContext,
        kind: ActivationKind,
    ) -> Option<ActivationEpochId> {
        let id = self.activation(source, scope, context, kind)?;
        self.active.push(id);
        Some(id)
    }

    pub(crate) fn leave(&mut self, id: ActivationEpochId) {
        assert_eq!(self.active.pop(), Some(id));
        self.activations[id.0 as usize].end_expression = Some(self.expressions.len());
    }

    pub(crate) fn current_activation(&self) -> Option<ActivationEpochId> {
        self.active.last().copied()
    }

    pub(super) fn activation(
        &mut self,
        source: Option<ExprId>,
        scope: ScopeId,
        context: InvocationContext,
        kind: ActivationKind,
    ) -> Option<ActivationEpochId> {
        if !self.admit(1) {
            return None;
        }
        self.allocate_activation(source, scope, context, kind)
    }

    /// The caller has admitted the complete allocation/observation operation.
    pub(super) fn allocate_activation(
        &mut self,
        source: Option<ExprId>,
        scope: ScopeId,
        context: InvocationContext,
        kind: ActivationKind,
    ) -> Option<ActivationEpochId> {
        let id = ActivationEpochId(u32::try_from(self.activations.len()).ok()?);
        self.activations.push(EvaluationActivation {
            id,
            parent: self.current_activation(),
            kind,
            source,
            scope,
            context,
            start_expression: self.expressions.len(),
            end_expression: None,
            result: None,
        });
        Some(id)
    }
}
