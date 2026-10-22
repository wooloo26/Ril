//! Independent authentication of numeric term births and exact selections.
use super::solve::charge;
use super::*;
use crate::hir::nodes::{self as hir, HirProgram};
use crate::numeric_literals::{ExactLiteral, ParseLimit};
use crate::sema::{
    SemanticFacts,
    application_effect::{ActivationKind, EvaluationRecord},
};
use crate::sema::{
    context::FrozenEnvironment,
    source_types::{SourceSchema, WorkLimit},
};
use ril_syntax::ast::Literal;
use std::cell::{RefCell, RefMut};
use std::ops::{Deref, DerefMut};
#[path = "source_views.rs"]
mod source_views;

#[derive(Clone, Copy)]
pub(crate) enum NumericSourceTypes<'a> {
    Live(&'a crate::sema::source_types::LiveSourceTypes),
    Frozen(&'a crate::sema::source_types::SourceTypeIndex),
}

impl NumericSourceTypes<'_> {
    fn binding_schema(
        self,
        binding: usize,
        work: &mut WorkLimit,
    ) -> Result<Option<(SourceSchema, FrozenEnvironment)>, SourceTypesError> {
        match self {
            Self::Live(types) => types.binding_schema_if_known(binding, None, work),
            Self::Frozen(types) => types.binding_schema_if_known(binding, None, work),
        }
    }
    fn view_schema(
        self,
        view: crate::sema::source_types::SourceView,
        work: &mut WorkLimit,
    ) -> Result<(SourceSchema, FrozenEnvironment), SourceTypesError> {
        match self {
            Self::Live(types) => types.view_schema(view, work),
            Self::Frozen(types) => types.view_schema(view, work),
        }
    }
}

fn hir_error(error: hir::LowerError) -> SourceTypesError {
    match error {
        hir::LowerError::Budget(_) => SourceTypesError::BudgetExceeded,
        _ => SourceTypesError::Unresolved,
    }
}

fn has_numeric(value: &Value, work: &mut usize, depth: usize) -> Result<bool, SourceTypesError> {
    charge(work, 1)?;
    if depth >= 128 {
        return Err(SourceTypesError::BudgetExceeded);
    }
    if matches!(value.ty, Ty::NumericHole(_))
        || !value.numeric.uses.is_empty()
        || !value.numeric.selections.is_empty()
    {
        return Ok(true);
    }
    for child in [
        &value.option_payload,
        &value.result_payload,
        &value.result_success,
        &value.result_error,
        &value.variant_payload,
    ]
    .into_iter()
    .flatten()
    .chain(value.variant_witnesses.values())
    {
        if has_numeric(child, work, depth + 1)? {
            return Ok(true);
        }
    }
    Ok(false)
}

#[derive(Clone)]
pub(crate) struct NumericReplayInputs<'a> {
    pub(crate) semantic_hir: Option<&'a HirProgram>,
    pub(crate) target_layout: Option<TargetLayout>,
    pub(crate) numeric_holes: &'a [NumericHole],
    pub(crate) numeric_uses: &'a [NumericUse],
    pub(crate) numeric_selections: &'a [NumericSelection],
    pub(crate) activations: &'a [crate::sema::application_effect::EvaluationActivation],
    pub(crate) evaluations: &'a [EvaluationRecord],
    pub(crate) expressions: &'a [crate::sema::ExpressionFact],
    pub(crate) allocation_history: &'a [(crate::sema::facts::NodeId, crate::sema::facts::NodeId)],
    pub(crate) bindings: &'a [crate::sema::model::BindingInfo],
    pub(crate) constructors: &'a BTreeMap<String, crate::sema::model::ConstructorInfo>,
    pub(crate) source_types: NumericSourceTypes<'a>,
    pub(crate) witnesses: &'a [crate::sema::effect_identity::InvocationWitness],
    pub(crate) explanations: &'a crate::sema::facts::Explanations,
    pub(crate) open: Option<ril_compiler_core::ids::ActivationEpochId>,
    pub(crate) session: Option<&'a RefCell<NumericReplaySession>>,
    pub(crate) subject: Option<&'a crate::sema::evaluated::EvaluatedValue>,
    pub(crate) frozen: Option<&'a SemanticFacts>,
    pub(crate) query: Option<std::rc::Rc<crate::sema::source_query::SourceQuery>>,
}

impl<'a> NumericReplayInputs<'a> {
    pub(crate) fn from_facts(facts: &'a SemanticFacts) -> Self {
        Self {
            semantic_hir: facts.semantic_hir.as_deref(),
            target_layout: facts.target_layout,
            numeric_holes: &facts.numeric_holes,
            numeric_uses: &facts.numeric_uses,
            numeric_selections: &facts.numeric_selections,
            activations: &facts.activations,
            evaluations: &facts.evaluations,
            expressions: &facts.expressions,
            allocation_history: &facts.allocation_history,
            bindings: &facts.bindings,
            constructors: &facts.constructors,
            source_types: NumericSourceTypes::Frozen(&facts.source_types),
            witnesses: &facts.invocation_witnesses,
            explanations: &facts.explanations,
            open: None,
            session: None,
            subject: None,
            frozen: Some(facts),
            query: None,
        }
    }
}

pub(crate) fn pattern_number_type_inputs(
    facts: NumericReplayInputs<'_>,
    pattern: PatternId,
    birth: NumericBirth,
    work: &mut usize,
) -> Result<NumberType, SourceTypesError> {
    Replay::new(facts, work)?.pattern_expected(pattern, birth)
}

#[cfg(test)]
pub(crate) fn checked_resolution_at(
    facts: &SemanticFacts,
    observation: EvaluationOccurrenceId,
    work: &mut usize,
) -> Result<Option<(NumericHoleId, Arc<NumericResolution>)>, SourceTypesError> {
    checked_resolution_at_inputs(NumericReplayInputs::from_facts(facts), observation, work)
}

#[cfg(test)]
pub(crate) fn checked_resolution_in_session(
    facts: &SemanticFacts,
    observation: EvaluationOccurrenceId,
    session: &RefCell<NumericReplaySession>,
    work: &mut usize,
) -> Result<Option<(NumericHoleId, Arc<NumericResolution>)>, SourceTypesError> {
    let mut inputs = NumericReplayInputs::from_facts(facts);
    inputs.session = Some(session);
    checked_resolution_at_inputs(inputs, observation, work)
}

pub(crate) fn checked_resolution_in_query(
    facts: &SemanticFacts,
    observation: EvaluationOccurrenceId,
    session: &RefCell<NumericReplaySession>,
    query: &std::rc::Rc<crate::sema::source_query::SourceQuery>,
    work: &mut usize,
) -> Result<Option<(NumericHoleId, Arc<NumericResolution>)>, SourceTypesError> {
    let mut inputs = NumericReplayInputs::from_facts(facts);
    inputs.session = Some(session);
    inputs.query = Some(query.clone());
    checked_resolution_at_inputs(inputs, observation, work)
}

pub(crate) fn checked_resolution_at_inputs(
    mut facts: NumericReplayInputs<'_>,
    observation: EvaluationOccurrenceId,
    work: &mut usize,
) -> Result<Option<(NumericHoleId, Arc<NumericResolution>)>, SourceTypesError> {
    charge(work, 1)?;
    let value = &facts
        .expressions
        .get(observation.0 as usize)
        .ok_or(SourceTypesError::MissingNode)?
        .value;
    let Ty::NumericHole(id) = value.ty else {
        return Ok(None);
    };
    let query = facts.query.clone().unwrap_or_default();
    let _entered = query.enter(
        crate::sema::source_query::QueryKind::Numeric,
        observation,
        work,
    )?;
    facts.query = Some(query);
    let mut replay = Replay::new(facts, work)?;
    replay.link(observation, id, 0)?;
    let resolution = replay.hole(id, 0)?;
    Ok(Some((id, resolution)))
}

pub(crate) fn validate(facts: &SemanticFacts, work: &mut usize) -> Result<(), SourceTypesError> {
    charge(work, 1)?;
    if facts.semantic_hir.is_none() {
        if !facts.numeric_holes.is_empty()
            || !facts.numeric_uses.is_empty()
            || !facts.numeric_selections.is_empty()
        {
            return Err(SourceTypesError::MissingNode);
        }
        for fact in &facts.expressions {
            if fact.source_id.is_some() || has_numeric(&fact.value, work, 0)? {
                return Err(SourceTypesError::MissingNode);
            }
        }
        return Ok(());
    }
    let mut replay = Replay::new(NumericReplayInputs::from_facts(facts), work)?;
    let mut births = BTreeSet::new();
    for (index, hole) in facts.numeric_holes.iter().enumerate() {
        charge(replay.work, 2)?;
        if hole.id.0 as usize != index {
            return Err(SourceTypesError::Unresolved);
        }
        let site = match hole.term {
            NumericTerm::Literal(id) => Some(
                facts
                    .numeric_uses
                    .get(id.0 as usize)
                    .ok_or(SourceTypesError::MissingNode)?
                    .site,
            ),
            _ => None,
        };
        if !births.insert((hole.birth.occurrence, site)) {
            return Err(SourceTypesError::Unresolved);
        }
        replay.hole(hole.id, 0)?;
    }
    for (index, use_) in facts.numeric_uses.iter().enumerate() {
        charge(replay.work, 1)?;
        if use_.id.0 as usize != index
            || !matches!(facts.numeric_holes.get(use_.hole.0 as usize).map(|h| &h.term), Some(NumericTerm::Literal(id)) if *id == use_.id)
        {
            return Err(SourceTypesError::Unresolved);
        }
    }
    for (index, selection) in facts.numeric_selections.iter().enumerate() {
        charge(replay.work, 1)?;
        if selection.id.0 as usize != index {
            return Err(SourceTypesError::Unresolved);
        }
        let use_ = facts
            .numeric_uses
            .get(selection.literal.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        let resolution = replay.hole(use_.hole, 0)?;
        if !resolution.dependencies.selections.contains(&selection.id) {
            return Err(SourceTypesError::Unresolved);
        }
    }
    for (index, fact) in facts.expressions.iter().enumerate() {
        charge(replay.work, 1)?;
        replay.value_dependencies(&fact.value, 0)?;
        replay.expression_coverage(EvaluationOccurrenceId(index as u32))?;
        if let Ty::NumericHole(hole) = fact.value.ty {
            replay.link(EvaluationOccurrenceId(index as u32), hole, 0)?;
        }
    }
    Ok(())
}

#[cfg(test)]
pub(super) fn validate_observation_coverage(
    facts: &SemanticFacts,
    observation: EvaluationOccurrenceId,
    work: &mut usize,
) -> Result<(), SourceTypesError> {
    Replay::new(NumericReplayInputs::from_facts(facts), work)?.expression_coverage(observation)
}

struct Replay<'a, 'w> {
    facts: NumericReplayInputs<'a>,
    hir: &'a HirProgram,
    work: &'w mut usize,
    active: BTreeSet<NumericHoleId>,
    checked: BTreeSet<NumericHoleId>,
    session: SessionAccess<'a>,
    expected: BTreeMap<NumericHoleId, NumericResolution>,
    schemas: BTreeMap<EvaluationOccurrenceId, (SourceSchema, FrozenEnvironment)>,
    sources: Option<crate::sema::record_bound_validation::OriginalOperandSources<'a>>,
    query: std::rc::Rc<crate::sema::source_query::SourceQuery>,
}

/// Derived indexes for one immutable facts query or one append-only producer.
/// No result/selection authorization is cached across queries.
type BindingHeaders = BTreeMap<
    PatternId,
    (
        Option<ril_compiler_core::ids::TypeExprId>,
        Option<Vec<crate::sema::source_types::SourcePath>>,
        ExprId,
    ),
>;
#[derive(Debug, Default)]
pub(crate) struct NumericReplaySession {
    hir_nodes: usize,
    generated_roots: usize,
    indexed_evaluations: usize,
    indexed_uses: usize,
    blocks: Option<crate::hir::blocks::BlockIndex>,
    children: BTreeMap<
        (Option<ril_compiler_core::ids::ActivationEpochId>, ExprId),
        Option<EvaluationOccurrenceId>,
    >,
    uses_by_occurrence: BTreeMap<OccurrenceIdentity, Option<NumericUseId>>,
    lexical: Option<crate::hir::lexical::LexicalBindings>,
    headers: BTreeMap<ril_compiler_core::ids::TypeExprId, SourceSchema>,
    pattern_roles: BTreeMap<(Option<ExprId>, PatternId), (ExprId, Vec<PatternStep>)>,
    pattern_owners: BTreeSet<Option<ExprId>>,
    pattern_statements: usize,
    binding_statements: usize,
    binding_headers: Option<BindingHeaders>,
}

enum SessionAccess<'a> {
    Shared(RefMut<'a, NumericReplaySession>),
    Owned(Box<NumericReplaySession>),
}
impl Deref for SessionAccess<'_> {
    type Target = NumericReplaySession;
    fn deref(&self) -> &Self::Target {
        match self {
            Self::Shared(session) => session,
            Self::Owned(session) => session,
        }
    }
}
impl DerefMut for SessionAccess<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Self::Shared(session) => session,
            Self::Owned(session) => session,
        }
    }
}

#[derive(Debug, Clone)]
enum PatternStep {
    Tuple(usize),
    Field(String),
    Constructor(String),
}

impl<'a, 'w> Replay<'a, 'w> {
    fn value_dependencies(&mut self, value: &Value, depth: usize) -> Result<(), SourceTypesError> {
        charge(self.work, 1)?;
        if depth >= 128 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        self.dependencies(&value.numeric)?;
        for child in [
            &value.option_payload,
            &value.result_payload,
            &value.result_success,
            &value.result_error,
            &value.variant_payload,
        ]
        .into_iter()
        .flatten()
        .chain(value.variant_witnesses.values())
        {
            self.value_dependencies(child, depth + 1)?;
        }
        Ok(())
    }

    fn expression_coverage(&mut self, id: EvaluationOccurrenceId) -> Result<(), SourceTypesError> {
        charge(self.work, 2)?;
        let row = self
            .facts
            .evaluations
            .get(id.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        let Some(identity) = row.identity else {
            return Ok(());
        };
        let activation = self
            .facts
            .activations
            .get(identity.activation.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        let record = self.record(id)?;
        let identity = record.identity.ok_or(SourceTypesError::MissingNode)?;
        let expression = self
            .hir
            .expression(identity.source)
            .ok_or(SourceTypesError::MissingNode)?;
        let literal = match &expression.kind {
            hir::ExprKind::Literal(literal @ (Literal::Integer(_) | Literal::Float(_))) => literal,
            hir::ExprKind::Unary { operator, operand } if operator == "-" => {
                match &self
                    .hir
                    .expression(*operand)
                    .ok_or(SourceTypesError::MissingNode)?
                    .kind
                {
                    hir::ExprKind::Literal(literal @ (Literal::Integer(_) | Literal::Float(_))) => {
                        literal
                    }
                    _ => return Ok(()),
                }
            }
            _ => return Ok(()),
        };
        if let Literal::Integer(text) | Literal::Float(text) = literal {
            charge(self.work, 1 + text.len())?;
        }
        if activation.kind == ActivationKind::Emission {
            // Only the real operand of an atomic signed literal is emitted
            // under its parent's receipt. Emission is not a coverage waiver.
            let parent_id = activation.parent.ok_or(SourceTypesError::MissingNode)?;
            let parent = self
                .facts
                .activations
                .get(parent_id.0 as usize)
                .filter(|parent| parent.id == parent_id)
                .ok_or(SourceTypesError::MissingNode)?;
            let minus = parent.source.ok_or(SourceTypesError::MissingNode)?;
            let use_id = self
                .session
                .uses_by_occurrence
                .get(&OccurrenceIdentity {
                    source: minus,
                    activation: parent_id,
                })
                .copied()
                .flatten()
                .ok_or(SourceTypesError::MissingNode)?;
            let usage = self
                .facts
                .numeric_uses
                .get(use_id.0 as usize)
                .ok_or(SourceTypesError::MissingNode)?;
            if !matches!(usage.site, NumericSite::Expression { literal, immediate_minus: Some(source) }
                if literal == identity.source && source == minus)
                || activation.scope != parent.scope
                || activation.context != parent.context
                || !self.facts.expressions[id.0 as usize]
                    .value
                    .numeric
                    .uses
                    .contains(&usage.id)
            {
                return Err(SourceTypesError::Unresolved);
            }
            self.hole(usage.hole, 0)?;
            return Ok(());
        }
        if activation.kind != ActivationKind::Expression {
            return Err(SourceTypesError::Unresolved);
        }
        charge(self.work, 1)?;
        let use_id = self
            .session
            .uses_by_occurrence
            .get(&identity)
            .copied()
            .flatten()
            .ok_or(SourceTypesError::MissingNode)?;
        let use_ = self
            .facts
            .numeric_uses
            .get(use_id.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        if !self.facts.expressions[id.0 as usize]
            .value
            .numeric
            .uses
            .contains(&use_.id)
        {
            return Err(SourceTypesError::Unresolved);
        }
        self.hole(use_.hole, 0)?;
        Ok(())
    }
    fn dependencies(&mut self, dependencies: &NumericDependencies) -> Result<(), SourceTypesError> {
        charge(
            self.work,
            dependencies.uses.len() + dependencies.selections.len(),
        )?;
        for id in &dependencies.uses {
            if self
                .facts
                .numeric_uses
                .get(id.0 as usize)
                .is_none_or(|row| row.id != *id)
            {
                return Err(SourceTypesError::MissingNode);
            }
        }
        for id in &dependencies.selections {
            let row = self
                .facts
                .numeric_selections
                .get(id.0 as usize)
                .filter(|row| row.id == *id)
                .ok_or(SourceTypesError::MissingNode)?;
            if !dependencies.uses.contains(&row.literal) {
                return Err(SourceTypesError::Unresolved);
            }
        }
        Ok(())
    }

    fn raw_dependencies(
        &mut self,
        hole: &NumericHole,
    ) -> Result<NumericDependencies, SourceTypesError> {
        let operands: Vec<&NumericOperand> = match &hole.term {
            NumericTerm::Literal(use_id) => {
                charge(self.work, 1)?;
                return Ok(NumericDependencies {
                    uses: [*use_id].into(),
                    selections: BTreeSet::new(),
                });
            }
            NumericTerm::Unary { operand, .. } => vec![operand],
            NumericTerm::Binary { left, right, .. } => vec![left, right],
            NumericTerm::Join(_) => return Err(SourceTypesError::Unresolved),
        };
        let mut result = NumericDependencies::default();
        for operand in operands {
            charge(
                self.work,
                1 + operand.dependencies.uses.len() + operand.dependencies.selections.len(),
            )?;
            result.include(&operand.dependencies);
        }
        Ok(result)
    }
    fn new(facts: NumericReplayInputs<'a>, work: &'w mut usize) -> Result<Self, SourceTypesError> {
        charge(work, 1)?;
        let query = facts.query.clone().unwrap_or_default();
        let mut session = match facts.session {
            Some(session) => SessionAccess::Shared(
                session
                    .try_borrow_mut()
                    .map_err(|_| SourceTypesError::Unresolved)?,
            ),
            None => SessionAccess::Owned(Box::default()),
        };
        let hir = facts.semantic_hir.ok_or(SourceTypesError::MissingNode)?;
        if session.hir_nodes > hir.node_count()
            || session.generated_roots > hir.generated_roots().len()
        {
            return Err(SourceTypesError::Unresolved);
        }
        if session.hir_nodes != hir.node_count() {
            session.blocks = None;
            session.pattern_owners.remove(&None);
        }
        if let Some(lexical) = &mut session.lexical {
            lexical.refresh_generated(hir, work).map_err(hir_error)?;
        }
        session.hir_nodes = hir.node_count();
        session.generated_roots = hir.generated_roots().len();
        if session.indexed_evaluations > facts.evaluations.len()
            || session.indexed_uses > facts.numeric_uses.len()
        {
            return Err(SourceTypesError::Unresolved);
        }
        // Observations are appended only after their activation has a result.
        // Indexing the activation prefix would miss open ancestors forever.
        for record in &facts.evaluations[session.indexed_evaluations..] {
            charge(
                work,
                3 + session.children.len().checked_ilog2().unwrap_or(0) as usize,
            )?;
            let Some(identity) = record.identity else {
                session.indexed_evaluations += 1;
                continue;
            };
            let activation = facts
                .activations
                .get(identity.activation.0 as usize)
                .ok_or(SourceTypesError::MissingNode)?;
            if record.id.0 as usize != session.indexed_evaluations
                || activation.id != identity.activation
                || activation.source != Some(identity.source)
                || activation.result != Some(record.id)
            {
                return Err(SourceTypesError::Unresolved);
            }
            if activation.kind != ActivationKind::Emission
                && let (parent, Some(source), Some(result)) =
                    (activation.parent, activation.source, activation.result)
            {
                session
                    .children
                    .entry((parent, source))
                    .and_modify(|entry| *entry = None)
                    .or_insert(Some(result));
            }
            session.indexed_evaluations += 1;
        }
        for use_ in &facts.numeric_uses[session.indexed_uses..] {
            charge(
                work,
                2 + session
                    .uses_by_occurrence
                    .len()
                    .checked_ilog2()
                    .unwrap_or(0) as usize,
            )?;
            session
                .uses_by_occurrence
                .entry(use_.birth.occurrence)
                .and_modify(|entry| *entry = None)
                .or_insert(Some(use_.id));
            session.indexed_uses += 1;
        }
        Ok(Self {
            facts,
            hir,
            work,
            active: BTreeSet::new(),
            checked: BTreeSet::new(),
            session,
            expected: BTreeMap::new(),
            schemas: BTreeMap::new(),
            sources: None,
            query,
        })
    }

    fn record(
        &mut self,
        observation: EvaluationOccurrenceId,
    ) -> Result<&'a EvaluationRecord, SourceTypesError> {
        charge(self.work, 3)?;
        let record = self
            .facts
            .evaluations
            .get(observation.0 as usize)
            .filter(|r| r.id == observation)
            .ok_or(SourceTypesError::MissingNode)?;
        let identity = record.identity.ok_or(SourceTypesError::MissingNode)?;
        let fact = self
            .facts
            .expressions
            .get(observation.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        let activation = self
            .facts
            .activations
            .get(identity.activation.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        if activation.id != identity.activation
            || activation.source != Some(identity.source)
            || activation.context != record.context
            || activation.scope != record.scope
            || activation.result != Some(record.id)
            || fact.source_id != Some(identity.source)
            || fact.allocation_epoch != record.allocation_epoch
            || record.allocation_epoch > self.facts.allocation_history.len()
        {
            return Err(SourceTypesError::Unresolved);
        }
        Ok(record)
    }

    fn birth(&mut self, birth: NumericBirth) -> Result<EvaluationOccurrenceId, SourceTypesError> {
        charge(self.work, 2)?;
        let activation = self
            .facts
            .activations
            .get(birth.occurrence.activation.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        let result = activation.result.ok_or(SourceTypesError::MissingNode)?;
        let record = self.record(result)?;
        if record.identity != Some(birth.occurrence)
            || record.scope != birth.scope
            || record.context != birth.context
            || activation.kind != ActivationKind::Expression
            || birth.allocation_epoch != record.allocation_epoch
        {
            return Err(SourceTypesError::Unresolved);
        }
        Ok(result)
    }

    fn child(
        &mut self,
        parent: NumericBirth,
        source: ExprId,
    ) -> Result<EvaluationOccurrenceId, SourceTypesError> {
        charge(self.work, 1)?;
        let id = self
            .session
            .children
            .get(&(Some(parent.occurrence.activation), source))
            .copied()
            .flatten()
            .ok_or(SourceTypesError::MissingNode)?;
        let record = self.record(id)?;
        let identity = record.identity.ok_or(SourceTypesError::MissingNode)?;
        let child = self
            .facts
            .activations
            .get(identity.activation.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        if child.context != parent.context
            || child.scope != parent.scope
            || identity.source != source
            || child.parent != Some(parent.occurrence.activation)
        {
            return Err(SourceTypesError::Unresolved);
        }
        Ok(id)
    }

    fn literal(&mut self, use_: &NumericUse) -> Result<(), SourceTypesError> {
        charge(self.work, 2)?;
        let (literal, negative) = match use_.site {
            NumericSite::Expression {
                literal,
                immediate_minus,
            } => {
                if use_.birth.occurrence.source != immediate_minus.unwrap_or(literal) {
                    return Err(SourceTypesError::Unresolved);
                }
                if let Some(source) = immediate_minus
                    && !matches!(&self.hir.expression(source).ok_or(SourceTypesError::MissingNode)?.kind, hir::ExprKind::Unary { operator, operand } if operator == "-" && *operand == literal)
                {
                    return Err(SourceTypesError::Unresolved);
                }
                let hir::ExprKind::Literal(literal) = &self
                    .hir
                    .expression(literal)
                    .ok_or(SourceTypesError::MissingNode)?
                    .kind
                else {
                    return Err(SourceTypesError::Unresolved);
                };
                (literal, immediate_minus.is_some())
            }
            NumericSite::Pattern(pattern) => {
                let hir::PatternKind::Literal(literal) = &self
                    .hir
                    .pattern(pattern)
                    .ok_or(SourceTypesError::MissingNode)?
                    .kind
                else {
                    return Err(SourceTypesError::Unresolved);
                };
                let generated = self
                    .hir
                    .expression(use_.birth.occurrence.source)
                    .ok_or(SourceTypesError::MissingNode)?;
                let literal_len = |literal: &Literal| match literal {
                    Literal::Integer(text)
                    | Literal::Float(text)
                    | Literal::String(text)
                    | Literal::RawString(text)
                    | Literal::Bytes(text) => text.len(),
                    Literal::Bool(_) | Literal::Unit => 0,
                };
                charge(self.work, 1 + literal_len(literal))?;
                if let hir::ExprKind::Literal(actual) = &generated.kind {
                    charge(self.work, 1 + literal_len(actual))?;
                }
                if !matches!(generated.info.origin, hir::NodeOrigin::Generated { anchor: hir::NodeId::Pattern(actual), kind: hir::GeneratedKind::PatternValue, .. } if actual == pattern)
                    || !matches!(&generated.kind, hir::ExprKind::Literal(actual) if actual == literal)
                {
                    return Err(SourceTypesError::Unresolved);
                }
                let hir::NodeOrigin::Generated { generation, .. } = generated.info.origin else {
                    return Err(SourceTypesError::Unresolved);
                };
                if self.hir.generated_roots().get(generation as usize)
                    != Some(&hir::NodeId::Expr(use_.birth.occurrence.source))
                {
                    return Err(SourceTypesError::Unresolved);
                }
                let expected = self.pattern_expected(pattern, use_.birth)?;
                let hole = self
                    .facts
                    .numeric_holes
                    .get(use_.hole.0 as usize)
                    .ok_or(SourceTypesError::MissingNode)?;
                let NumericHoleState::Committed { resolution, .. } = &hole.state else {
                    return Err(SourceTypesError::Unresolved);
                };
                if expected != resolution.number_type {
                    return Err(SourceTypesError::Unresolved);
                }
                (literal, false)
            }
        };
        let (text, integer) = match literal {
            Literal::Integer(text) => (text, true),
            Literal::Float(text) => (text, false),
            _ => return Err(SourceTypesError::Unresolved),
        };
        charge(self.work, text.len().saturating_mul(4).saturating_add(1))?;
        let exact = if integer {
            ExactLiteral::integer(
                text,
                negative,
                ParseLimit {
                    max_bytes: 1_048_576,
                },
            )
        } else {
            ExactLiteral::decimal(
                text,
                negative,
                ParseLimit {
                    max_bytes: 1_048_576,
                },
            )
        }
        .map_err(|_| SourceTypesError::Unresolved)?;
        if exact != use_.exact {
            return Err(SourceTypesError::Unresolved);
        }
        Ok(())
    }

    fn index_pattern_role(
        &mut self,
        owner: Option<ExprId>,
        root: PatternId,
        source: ExprId,
        path: &mut Vec<PatternStep>,
        depth: usize,
    ) -> Result<(), SourceTypesError> {
        charge(
            self.work,
            3 + path.len()
                + self
                    .session
                    .pattern_roles
                    .len()
                    .checked_ilog2()
                    .unwrap_or(0) as usize,
        )?;
        if depth >= 128 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        for step in path.iter() {
            if let PatternStep::Field(name) | PatternStep::Constructor(name) = step {
                charge(self.work, name.len())?;
            }
        }
        if self
            .session
            .pattern_roles
            .insert((owner, root), (source, path.clone()))
            .is_some()
        {
            return Err(SourceTypesError::Unresolved);
        }
        let hir = self.hir;
        let node = hir.pattern(root).ok_or(SourceTypesError::MissingNode)?;
        match &node.kind {
            hir::PatternKind::Mode { pattern, .. } => {
                self.index_pattern_role(owner, *pattern, source, path, depth + 1)?
            }
            hir::PatternKind::Alternative(items) => {
                for child in items {
                    self.index_pattern_role(owner, *child, source, path, depth + 1)?;
                }
            }
            hir::PatternKind::Tuple(items) => {
                for (index, child) in items.iter().enumerate() {
                    charge(self.work, 1)?;
                    path.push(PatternStep::Tuple(index));
                    self.index_pattern_role(owner, *child, source, path, depth + 1)?;
                    path.pop();
                }
            }
            hir::PatternKind::Record { fields, .. } => {
                for field in fields {
                    charge(self.work, 1 + field.name.len())?;
                    path.push(PatternStep::Field(field.name.clone()));
                    self.index_pattern_role(owner, field.pattern, source, path, depth + 1)?;
                    path.pop();
                }
            }
            hir::PatternKind::Constructor {
                path: names,
                arguments,
                ..
            } => {
                charge(self.work, names.len() + 1)?;
                for name in names {
                    charge(self.work, name.len())?;
                }
                path.push(PatternStep::Constructor(names.join("::")));
                for (index, child) in arguments.iter().enumerate() {
                    if arguments.len() != 1 {
                        charge(self.work, 1)?;
                        path.push(PatternStep::Tuple(index));
                    }
                    self.index_pattern_role(owner, *child, source, path, depth + 1)?;
                    if arguments.len() != 1 {
                        path.pop();
                    }
                }
                path.pop();
            }
            _ => {}
        }
        Ok(())
    }

    fn pattern_roles(&mut self, owner: Option<ExprId>) -> Result<(), SourceTypesError> {
        charge(self.work, 1)?;
        if self.session.pattern_owners.contains(&owner) {
            return Ok(());
        }
        let hir = self.hir;
        if let Some(owner) = owner {
            match &hir
                .expression(owner)
                .ok_or(SourceTypesError::MissingNode)?
                .kind
            {
                hir::ExprKind::Match { value, arms, .. } => {
                    charge(self.work, arms.len())?;
                    for arm in arms {
                        self.index_pattern_role(
                            Some(owner),
                            arm.pattern,
                            *value,
                            &mut Vec::new(),
                            0,
                        )?;
                    }
                }
                hir::ExprKind::Is { value, pattern } => {
                    self.index_pattern_role(Some(owner), *pattern, *value, &mut Vec::new(), 0)?
                }
                _ => return Err(SourceTypesError::Unresolved),
            }
        } else {
            let total = hir.statements().len();
            charge(
                self.work,
                total
                    .checked_sub(self.session.pattern_statements)
                    .ok_or(SourceTypesError::Unresolved)?,
            )?;
            for (_, statement) in hir.statements().skip(self.session.pattern_statements) {
                if let hir::StmtKind::Binding { pattern, value, .. } = statement.kind {
                    self.index_pattern_role(None, pattern, value, &mut Vec::new(), 0)?;
                }
                self.session.pattern_statements += 1;
            }
        }
        charge(self.work, 1)?;
        self.session.pattern_owners.insert(owner);
        Ok(())
    }

    fn pattern_expected(
        &mut self,
        pattern: PatternId,
        birth: NumericBirth,
    ) -> Result<NumberType, SourceTypesError> {
        charge(self.work, 3)?;
        let generated = self
            .facts
            .activations
            .get(birth.occurrence.activation.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        if generated.id != birth.occurrence.activation
            || generated.source != Some(birth.occurrence.source)
            || generated.scope != birth.scope
            || generated.context != birth.context
        {
            return Err(SourceTypesError::Unresolved);
        }
        let parent = generated
            .parent
            .and_then(|id| self.facts.activations.get(id.0 as usize));
        let owner = parent.and_then(|parent| parent.source).filter(|id| {
            self.hir.expression(*id).is_some_and(|node| {
                matches!(
                    node.kind,
                    hir::ExprKind::Match { .. } | hir::ExprKind::Is { .. }
                )
            })
        });
        self.pattern_roles(owner)?;
        let (source, path) = self
            .session
            .pattern_roles
            .get(&(owner, pattern))
            .ok_or(SourceTypesError::MissingNode)?;
        charge(self.work, 2 + path.len())?;
        for step in path {
            if let PatternStep::Field(name) | PatternStep::Constructor(name) = step {
                charge(self.work, name.len())?;
            }
        }
        let (source, path) = (*source, path.clone());
        charge(
            self.work,
            2 + self.session.children.len().checked_ilog2().unwrap_or(0) as usize,
        )?;
        let observation = self
            .session
            .children
            .get(&(generated.parent, source))
            .copied()
            .flatten()
            .ok_or(SourceTypesError::MissingNode)?;
        let record = self.record(observation)?;
        let identity = record.identity.ok_or(SourceTypesError::MissingNode)?;
        let subject = self
            .facts
            .activations
            .get(identity.activation.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        if identity.source != source
            || subject.parent != generated.parent
            || record.context != birth.context
            || record.scope != birth.scope
            || observation.0 as usize >= generated.start_expression
        {
            return Err(SourceTypesError::Unresolved);
        }
        let (schema, environment) = self.subject_schema(observation, 0)?;
        if environment.is_poisoned() {
            return Err(SourceTypesError::Unresolved);
        }
        let schema = self.project_pattern_schema(schema, &path)?;
        let scalar = self
            .graph_work(|budget| schema.scalar_representation(budget))?
            .ok_or(SourceTypesError::Unresolved)?;
        super::source_number_type(scalar).ok_or(SourceTypesError::Unresolved)
    }
    fn operand(
        &mut self,
        parent: NumericBirth,
        source: ExprId,
        operand: &NumericOperand,
        depth: usize,
    ) -> Result<(), SourceTypesError> {
        let id = self.child(parent, source)?;
        if id != operand.observation {
            return Err(SourceTypesError::Unresolved);
        }
        let record = self.record(id)?;
        if record.allocation_epoch > parent.allocation_epoch {
            return Err(SourceTypesError::Unresolved);
        }
        let actual = &self.facts.expressions[id.0 as usize].value;
        crate::sema::clone_work::ty(self.work, &actual.ty, 0)
            .ok_or(SourceTypesError::BudgetExceeded)?;
        crate::sema::clone_work::ty(self.work, &operand.ty, 0)
            .ok_or(SourceTypesError::BudgetExceeded)?;
        charge(
            self.work,
            4 + actual.numeric.uses.len()
                + actual.numeric.selections.len()
                + operand.dependencies.uses.len()
                + operand.dependencies.selections.len(),
        )?;
        let expected_hole = match actual.ty {
            Ty::NumericHole(id) => Some(id),
            _ => None,
        };
        if expected_hole != operand.hole || operand.encoded.is_some() {
            return Err(SourceTypesError::Unresolved);
        }
        if let Some(hole) = operand.hole {
            self.link(id, hole, depth + 1)?;
            let resolution = self.hole(hole, depth + 1)?;
            if operand.ty == Ty::NumericHole(hole) {
                if operand.constant != actual.constant || operand.dependencies != actual.numeric {
                    return Err(SourceTypesError::Unresolved);
                }
            } else if operand.ty != resolution.value_type()
                || operand.constant != resolution.constant
                || operand.dependencies != resolution.dependencies
            {
                return Err(SourceTypesError::Unresolved);
            }
        } else if operand.ty != actual.ty
            || operand.constant != actual.constant
            || operand.dependencies != actual.numeric
        {
            return Err(SourceTypesError::Unresolved);
        }
        Ok(())
    }

    fn hole(
        &mut self,
        id: NumericHoleId,
        depth: usize,
    ) -> Result<Arc<NumericResolution>, SourceTypesError> {
        charge(self.work, 1)?;
        if depth >= 128 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let hole = self
            .facts
            .numeric_holes
            .get(id.0 as usize)
            .filter(|h| h.id == id)
            .ok_or(SourceTypesError::MissingNode)?;
        let NumericHoleState::Committed { resolution, .. } = &hole.state else {
            return Err(SourceTypesError::Unresolved);
        };
        if self.checked.contains(&id) {
            return Ok(resolution.clone());
        }
        if !self.active.insert(id) {
            return Err(SourceTypesError::Unresolved);
        }
        let observation = self.birth(hole.birth)?;
        let original = self
            .hir
            .expression(hole.birth.occurrence.source)
            .ok_or(SourceTypesError::MissingNode)?;
        match &hole.term {
            NumericTerm::Literal(use_id) => {
                let use_ = self
                    .facts
                    .numeric_uses
                    .get(use_id.0 as usize)
                    .filter(|u| u.id == *use_id && u.hole == id && u.birth == hole.birth)
                    .ok_or(SourceTypesError::MissingNode)?;
                self.literal(use_)?;
            }
            NumericTerm::Unary { operator, operand } => {
                let hir::ExprKind::Unary {
                    operator: actual,
                    operand: source,
                } = &original.kind
                else {
                    return Err(SourceTypesError::Unresolved);
                };
                charge(
                    self.work,
                    actual
                        .len()
                        .saturating_add(operator.len())
                        .saturating_add(1),
                )?;
                if actual != operator {
                    return Err(SourceTypesError::Unresolved);
                }
                self.operand(hole.birth, *source, operand, depth)?;
            }
            NumericTerm::Binary {
                operator,
                left,
                right,
            } => {
                let hir::ExprKind::Binary {
                    operator: actual,
                    left: a,
                    right: b,
                } = &original.kind
                else {
                    return Err(SourceTypesError::Unresolved);
                };
                charge(
                    self.work,
                    actual
                        .len()
                        .saturating_add(operator.len())
                        .saturating_add(1),
                )?;
                if actual != operator {
                    return Err(SourceTypesError::Unresolved);
                }
                self.operand(hole.birth, *a, left, depth)?;
                self.operand(hole.birth, *b, right, depth)?;
            }
            NumericTerm::Join(_) => return Err(SourceTypesError::Unresolved),
        }
        let expected = evaluate_cached(
            NumericInputs {
                holes: self.facts.numeric_holes,
                uses: self.facts.numeric_uses,
                selections: self.facts.numeric_selections,
                layout: self
                    .facts
                    .target_layout
                    .ok_or(SourceTypesError::MissingNode)?,
            },
            id,
            resolution.number_type,
            self.work,
            &mut self.expected,
        )?;
        charge(
            self.work,
            expected.dependencies.uses.len()
                + expected.dependencies.selections.len()
                + resolution.dependencies.uses.len()
                + resolution.dependencies.selections.len()
                + 1,
        )?;
        if expected != **resolution {
            return Err(SourceTypesError::Unresolved);
        }
        {
            let value = &self.facts.expressions[observation.0 as usize].value;
            if value.ty == Ty::NumericHole(id) {
                let dependencies = self.raw_dependencies(hole)?;
                if value.constant.is_some() || value.numeric != dependencies {
                    return Err(SourceTypesError::Unresolved);
                }
            } else if !resolution.matches_value(value, self.work)? {
                return Err(SourceTypesError::Unresolved);
            }
        }
        self.active.remove(&id);
        self.checked.insert(id);
        Ok(resolution.clone())
    }

    fn link(
        &mut self,
        observation: EvaluationOccurrenceId,
        id: NumericHoleId,
        depth: usize,
    ) -> Result<(), SourceTypesError> {
        charge(self.work, 1)?;
        if depth >= 128 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let record = self.record(observation)?;
        let identity = record.identity.ok_or(SourceTypesError::MissingNode)?;
        let hole = self
            .facts
            .numeric_holes
            .get(id.0 as usize)
            .filter(|h| h.id == id)
            .ok_or(SourceTypesError::MissingNode)?;
        let fact = &self.facts.expressions[observation.0 as usize];
        if fact.value.ty != Ty::NumericHole(id) {
            return Err(SourceTypesError::Unresolved);
        }
        if fact.value.numeric != self.raw_dependencies(hole)? {
            return Err(SourceTypesError::Unresolved);
        }
        if identity == hole.birth.occurrence {
            return Ok(());
        }
        let activation = &self.facts.activations[identity.activation.0 as usize];
        if activation.kind == ActivationKind::Emission {
            if let NumericTerm::Literal(use_id) = hole.term {
                let use_ = self
                    .facts
                    .numeric_uses
                    .get(use_id.0 as usize)
                    .ok_or(SourceTypesError::MissingNode)?;
                if matches!(use_.site, NumericSite::Expression { literal, immediate_minus: Some(minus) } if literal == identity.source && minus == hole.birth.occurrence.source)
                    && activation.parent == Some(hole.birth.occurrence.activation)
                    && record.context == hole.birth.context
                {
                    return Ok(());
                }
            }
            return Err(SourceTypesError::Unresolved);
        }
        match &self
            .hir
            .expression(identity.source)
            .ok_or(SourceTypesError::MissingNode)?
            .kind
        {
            hir::ExprKind::Block(_) => {
                if self.session.blocks.is_none() {
                    self.session.blocks = Some(
                        crate::hir::blocks::BlockIndex::new_with_budget(self.hir, self.work)
                            .map_err(|_| SourceTypesError::BudgetExceeded)?,
                    );
                }
                let (_, tail) = self
                    .session
                    .blocks
                    .as_ref()
                    .ok_or(SourceTypesError::MissingNode)?
                    .tail_with_budget(
                        ril_compiler_core::ids::BlockAnchor::ExpressionBody(identity.source),
                        self.work,
                    )
                    .map_err(|_| SourceTypesError::Unresolved)?
                    .ok_or(SourceTypesError::MissingNode)?;
                let birth = NumericBirth {
                    occurrence: identity,
                    scope: record.scope,
                    context: record.context,
                    allocation_epoch: record.allocation_epoch,
                };
                let child = self.child(birth, tail)?;
                self.link(child, id, depth + 1)
            }
            hir::ExprKind::Name(name) => {
                if fact.value.sources.len() != 1 {
                    return Err(SourceTypesError::Unresolved);
                }
                let binding_id = *fact
                    .value
                    .sources
                    .first()
                    .ok_or(SourceTypesError::MissingNode)?;
                let binding = self
                    .facts
                    .bindings
                    .get(binding_id)
                    .ok_or(SourceTypesError::MissingNode)?;
                charge(self.work, 1 + name.len() + binding.name.len())?;
                if binding.name != *name
                    || binding.parameter
                    || binding.owner != record.scope
                    || binding.context != record.context
                {
                    return Err(SourceTypesError::Unresolved);
                }
                let pattern = binding.pattern.ok_or(SourceTypesError::MissingNode)?;
                if self.session.lexical.is_none() {
                    self.session.lexical = Some(
                        crate::hir::lexical::LexicalBindings::new(self.hir, self.work)
                            .map_err(hir_error)?,
                    );
                }
                if self
                    .session
                    .lexical
                    .as_ref()
                    .ok_or(SourceTypesError::MissingNode)?
                    .lookup(identity.source, self.work)
                    .map_err(hir_error)?
                    != Some(pattern)
                {
                    return Err(SourceTypesError::Unresolved);
                }
                if let hir::PatternKind::Name(actual) = &self
                    .hir
                    .pattern(pattern)
                    .ok_or(SourceTypesError::MissingNode)?
                    .kind
                {
                    charge(self.work, actual.len())?;
                }
                if !matches!(&self.hir.pattern(pattern).ok_or(SourceTypesError::MissingNode)?.kind, hir::PatternKind::Name(actual) if actual == name)
                {
                    return Err(SourceTypesError::Unresolved);
                }
                let birth = binding.birth.ok_or(SourceTypesError::MissingNode)?;
                let (_, path, source) = self.local_binding_header(pattern)?;
                if source != birth.source || !path.is_empty() {
                    return Err(SourceTypesError::Unresolved);
                }
                let origin = self
                    .facts
                    .activations
                    .get(birth.activation.0 as usize)
                    .filter(|a| {
                        a.source == Some(birth.source)
                            && a.scope == binding.owner
                            && a.context == binding.context
                    })
                    .and_then(|a| a.result)
                    .ok_or(SourceTypesError::MissingNode)?;
                self.link(origin, id, depth + 1)
            }
            _ => Err(SourceTypesError::Unresolved),
        }
    }
}
