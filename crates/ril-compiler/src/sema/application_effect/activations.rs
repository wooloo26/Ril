//! Enter-time evaluation identities, independent of postorder value emissions.
use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActivationKind {
    Expression,
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
        let id = self.activation(source, scope, context, ActivationKind::Expression)?;
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

pub(super) fn validate(facts: &SemanticFacts) -> Result<(), String> {
    if facts.activations.len() != facts.evaluations.len() || facts.activations.len() > 1_000_000 {
        return Err("evaluation activation arena has incomplete coverage".into());
    }
    let mut stack: Vec<&EvaluationActivation> = Vec::new();
    let mut results = BTreeSet::new();
    for (ordinal, activation) in facts.activations.iter().enumerate() {
        let result = activation
            .result
            .ok_or("evaluation activation has no completed root")?;
        let end = activation
            .end_expression
            .ok_or("evaluation activation has no completed interval")?;
        while stack
            .last()
            .is_some_and(|parent| parent.end_expression.unwrap() <= activation.start_expression)
        {
            stack.pop();
        }
        if activation.id.0 as usize != ordinal
            || activation.parent != stack.last().map(|parent| parent.id)
            || activation.start_expression > result.0 as usize
            || result.0 as usize >= end
            || end > facts.evaluations.len()
            || stack
                .last()
                .is_some_and(|parent| end > parent.end_expression.unwrap())
            || (activation.kind == ActivationKind::Emission
                && activation.start_expression != result.0 as usize)
            || !results.insert(result)
        {
            return Err(
                "evaluation activation changed its parent, interval or arena identity".into(),
            );
        }
        let record = facts
            .evaluations
            .get(result.0 as usize)
            .ok_or("activation result is outside the value arena")?;
        if record.identity.is_none_or(|identity| {
            identity.activation != activation.id || Some(identity.source) != activation.source
        }) || record.context != activation.context
            || record.scope != activation.scope
        {
            return Err("activation root differs from its original evaluation or scope".into());
        }
        stack.push(activation);
    }
    Ok(())
}
