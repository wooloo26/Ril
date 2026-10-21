//! Original path syntax and actual read occurrences jointly select Source.
//! This borrowed query contains no producer cache, span key or erased type.
use super::{SourceTypesError, WorkLimit};
use crate::hir::nodes::{ExprKind, HirProgram};
use crate::sema::model::{Constant, StaticCoordinate};
use crate::sema::{
    ExpressionFact, SemanticFacts,
    application_effect::{
        ActivationKind, EvaluationActivation, EvaluationRecord, OccurrenceIdentity,
    },
    effect_identity::{InvocationContext, InvocationWitness, InvocationWitnessKind},
    facts::{CauseKind, Explanations},
};
use ril_compiler_core::{
    diagnostic::CauseId,
    ids::{ActivationEpochId, EvaluationOccurrenceId, ExprId},
    projection::TypeProjection,
};
use std::collections::BTreeSet;

#[derive(Debug, Clone, Copy)]
pub(crate) struct ProjectionOccurrence {
    pub(crate) identity: OccurrenceIdentity,
    pub(crate) context: InvocationContext,
    pub(crate) cause: CauseId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SourceRead {
    /// The outer read's own optional layer is retained for another consumer.
    Raw,
    /// Include the outer read's independently justified implicit projection.
    Received,
}

#[derive(Debug)]
struct ProjectionStep {
    expression: ExprId,
    base: ExprId,
    projection: ReadProjection,
}

#[derive(Debug)]
enum ReadProjection {
    Direct(TypeProjection),
    Computed {
        key: ExprId,
        expected: StaticCoordinate,
    },
}

fn literal_coordinate(
    hir: &HirProgram,
    source: ExprId,
    work: &mut WorkLimit,
    depth: usize,
) -> Result<Option<StaticCoordinate>, SourceTypesError> {
    use ril_syntax::ast::Literal;
    work.charge(1)?;
    if depth >= 64 {
        return Err(SourceTypesError::BudgetExceeded);
    }
    Ok(
        match &hir
            .expression(source)
            .ok_or(SourceTypesError::MissingNode)?
            .kind
        {
            ExprKind::Literal(Literal::String(text)) => {
                work.text(text)?;
                let body = text
                    .get(1..text.len().saturating_sub(1))
                    .ok_or(SourceTypesError::Unresolved)?;
                Some(StaticCoordinate::Label(
                    crate::lower::decode_text(body).map_err(|_| SourceTypesError::Unresolved)?,
                ))
            }
            ExprKind::Literal(Literal::RawString(text)) => {
                work.text(text)?;
                Some(StaticCoordinate::Label(
                    text.get(1..text.len().saturating_sub(1))
                        .ok_or(SourceTypesError::Unresolved)?
                        .to_owned(),
                ))
            }
            ExprKind::Literal(Literal::Integer(text)) => {
                use crate::numeric_literals::{ExactLiteral, ParseLimit};
                use num_traits::ToPrimitive;
                work.text(text)?;
                let literal = ExactLiteral::integer(text, false, ParseLimit { max_bytes: 4096 })
                    .map_err(|error| {
                        if error == crate::numeric_literals::Error::ResourceLimit {
                            SourceTypesError::BudgetExceeded
                        } else {
                            SourceTypesError::Unresolved
                        }
                    })?;
                Some(StaticCoordinate::Index(
                    literal
                        .magnitude()
                        .and_then(ToPrimitive::to_i128)
                        .ok_or(SourceTypesError::MissingProjection)?,
                ))
            }
            ExprKind::Unary { operator, operand } if operator == "-" => {
                match literal_coordinate(hir, *operand, work, depth + 1)? {
                    Some(StaticCoordinate::Index(value)) => Some(StaticCoordinate::Index(
                        value
                            .checked_neg()
                            .ok_or(SourceTypesError::MissingProjection)?,
                    )),
                    _ => None,
                }
            }
            _ => None,
        },
    )
}

#[derive(Debug)]
pub(crate) struct ProjectionPlan {
    root: ExprId,
    name: String,
    steps: Vec<ProjectionStep>,
}

impl ProjectionPlan {
    pub(crate) fn root(&self) -> ExprId {
        self.root
    }
    pub(crate) fn name(&self) -> &str {
        &self.name
    }
}

pub(crate) struct SourceProjection {
    pub(crate) root: EvaluationOccurrenceId,
    pub(crate) steps: Vec<TypeProjection>,
}

/// A temporary plan over the original HIR. Every receiver step retains its
/// actual base ExprId, rather than guessing where an unwrap happened later.
pub(crate) fn projection_path(
    hir: &HirProgram,
    source: ExprId,
    work: &mut WorkLimit,
) -> Result<Option<ProjectionPlan>, SourceTypesError> {
    let mut cursor = source;
    let mut seen = BTreeSet::new();
    let mut steps = Vec::new();
    loop {
        work.charge(1)?;
        if seen.len() >= 128 || !seen.insert(cursor) {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let expression = hir
            .expression(cursor)
            .ok_or(SourceTypesError::MissingNode)?;
        let (base, projection) = match &expression.kind {
            ExprKind::Name(name) => {
                work.text(name)?;
                steps.reverse();
                return Ok(Some(ProjectionPlan {
                    root: cursor,
                    name: name.clone(),
                    steps,
                }));
            }
            ExprKind::Path(path) => {
                work.charge(path.len())?;
                for segment in path {
                    work.text(segment)?;
                }
                steps.reverse();
                return Ok(Some(ProjectionPlan {
                    root: cursor,
                    name: path.join("::"),
                    steps,
                }));
            }
            ExprKind::Field {
                base,
                field,
                safe: false,
            } => {
                work.text(field)?;
                let projection =
                    if !field.is_empty() && field.bytes().all(|byte| byte.is_ascii_digit()) {
                        TypeProjection::Tuple(
                            field
                                .parse()
                                .map_err(|_| SourceTypesError::MissingProjection)?,
                        )
                    } else {
                        TypeProjection::Field(field.clone())
                    };
                (*base, ReadProjection::Direct(projection))
            }
            ExprKind::Index {
                base, safe: false, ..
            } => (*base, ReadProjection::Direct(TypeProjection::Element)),
            ExprKind::ComputedField { base, key } => {
                let Some(expected) = literal_coordinate(hir, *key, work, 0)? else {
                    return Ok(None);
                };
                (
                    *base,
                    ReadProjection::Computed {
                        key: *key,
                        expected,
                    },
                )
            }
            _ => return Ok(None),
        };
        work.charge(1)?;
        steps.push(ProjectionStep {
            expression: cursor,
            base,
            projection,
        });
        cursor = base;
    }
}

pub(crate) struct ProjectionReceipts<'a> {
    pub(crate) activations: &'a [EvaluationActivation],
    pub(crate) evaluations: &'a [EvaluationRecord],
    pub(crate) expressions: &'a [ExpressionFact],
    pub(crate) witnesses: &'a [InvocationWitness],
    pub(crate) explanations: &'a Explanations,
    /// Only the producer's actual entered activation may have an open end.
    pub(crate) open: Option<ActivationEpochId>,
}

fn require(condition: bool) -> Result<(), SourceTypesError> {
    condition.then_some(()).ok_or(SourceTypesError::Unresolved)
}

impl<'a> ProjectionReceipts<'a> {
    pub(crate) fn from_facts(facts: &'a SemanticFacts) -> Self {
        Self {
            activations: &facts.activations,
            evaluations: &facts.evaluations,
            expressions: &facts.expressions,
            witnesses: &facts.invocation_witnesses,
            explanations: &facts.explanations,
            open: None,
        }
    }

    fn observation(
        &self,
        occurrence: ProjectionOccurrence,
        work: &mut WorkLimit,
    ) -> Result<(&'a EvaluationRecord, &'a EvaluationActivation), SourceTypesError> {
        work.charge(1)?;
        let activation = self
            .activations
            .get(occurrence.identity.activation.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        let result = activation.result.ok_or(SourceTypesError::MissingNode)?;
        let record = self
            .evaluations
            .get(result.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        let fact = self
            .expressions
            .get(result.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        require(
            activation.id == occurrence.identity.activation
                && activation.source == Some(occurrence.identity.source)
                && activation.context == occurrence.context
                && activation.kind == ActivationKind::Expression
                && record.id == result
                && record.identity == Some(occurrence.identity)
                && record.context == occurrence.context
                && record.scope == activation.scope
                && record.allocation_epoch == fact.allocation_epoch
                && fact.source_id == Some(occurrence.identity.source)
                && fact.value.cause == occurrence.cause
                && activation.start_expression <= result.0 as usize,
        )?;
        match activation.end_expression {
            Some(end) => require(
                (result.0 as usize) < end
                    && end <= self.evaluations.len()
                    && end <= self.expressions.len(),
            )?,
            None => require(self.open == Some(activation.id))?,
        }
        Ok((record, activation))
    }

    pub(crate) fn unwrap_depth(
        &self,
        occurrence: ProjectionOccurrence,
        work: &mut WorkLimit,
    ) -> Result<u32, SourceTypesError> {
        self.observation(occurrence, work)?;
        work.charge(self.witnesses.len())?;
        let mut found = false;
        for row in self.witnesses {
            let InvocationWitnessKind::ImplicitUnwrap(proof) = &row.kind else {
                continue;
            };
            if proof.occurrence != occurrence.identity {
                continue;
            }
            require(
                !found
                    && row.context == occurrence.context
                    && proof.cause == occurrence.cause
                    && proof.depth == 1
                    && proof.tags == ["Some"]
                    && self.explanations.kinds.get(proof.cause.0 as usize)
                        == Some(&CauseKind::Restriction)
                    && self
                        .explanations
                        .causes
                        .get(proof.cause.0 as usize)
                        .is_some_and(|cause| cause.id == proof.cause),
            )?;
            found = true;
        }
        Ok(u32::from(found))
    }

    fn child(
        &self,
        parent: ProjectionOccurrence,
        source: ExprId,
        work: &mut WorkLimit,
    ) -> Result<ProjectionOccurrence, SourceTypesError> {
        let (record, entered) = self.observation(parent, work)?;
        let start = entered.id.0 as usize + 1;
        let mut found = None;
        for activation in self
            .activations
            .get(start..)
            .ok_or(SourceTypesError::MissingNode)?
        {
            work.charge(1)?;
            // Allocation is preorder, emission is postorder. Later siblings
            // cannot be operands evaluated before this completed parent root.
            if activation.start_expression >= record.id.0 as usize {
                break;
            }
            if activation.parent != Some(entered.id)
                || activation.source != Some(source)
                || activation.kind != ActivationKind::Expression
            {
                continue;
            }
            require(
                found.is_none()
                    && activation.context == parent.context
                    && activation.scope == record.scope
                    && activation.start_expression >= entered.start_expression,
            )?;
            let result = activation.result.ok_or(SourceTypesError::MissingNode)?;
            require(
                result.0 < record.id.0
                    && activation
                        .end_expression
                        .is_some_and(|end| end <= record.id.0 as usize),
            )?;
            let child = self
                .evaluations
                .get(result.0 as usize)
                .ok_or(SourceTypesError::MissingNode)?;
            require(child.scope == record.scope)?;
            let fact = self
                .expressions
                .get(result.0 as usize)
                .ok_or(SourceTypesError::MissingNode)?;
            let occurrence = ProjectionOccurrence {
                identity: child.identity.ok_or(SourceTypesError::MissingNode)?,
                context: child.context,
                cause: fact.value.cause,
            };
            require(
                occurrence.identity.activation == activation.id
                    && occurrence.identity.source == source,
            )?;
            self.observation(occurrence, work)?;
            found = Some(occurrence);
        }
        found.ok_or(SourceTypesError::MissingNode)
    }

    pub(crate) fn project(
        &self,
        plan: &ProjectionPlan,
        outer: ProjectionOccurrence,
        view: SourceRead,
        work: &mut WorkLimit,
    ) -> Result<SourceProjection, SourceTypesError> {
        self.observation(outer, work)?;
        work.charge(plan.steps.len() + 1)?;
        let mut reads = Vec::with_capacity(plan.steps.len() + 1);
        let mut current = outer;
        reads.push(current);
        for step in plan.steps.iter().rev() {
            require(current.identity.source == step.expression)?;
            current = self.child(current, step.base, work)?;
            reads.push(current);
        }
        require(current.identity.source == plan.root)?;
        let (root, _) = self.observation(current, work)?;
        reads.reverse();
        work.charge(2 * plan.steps.len() + 1)?;
        let mut steps = Vec::with_capacity(2 * plan.steps.len() + 1);
        for (index, (step, base)) in plan.steps.iter().zip(&reads).enumerate() {
            require(base.identity.source == step.base)?;
            if self.unwrap_depth(*base, work)? == 1 {
                steps.push(TypeProjection::OptionalPayload);
            }
            let projection = match &step.projection {
                ReadProjection::Direct(projection) => {
                    if let TypeProjection::Field(name) = projection {
                        work.text(name)?;
                    }
                    projection.clone()
                }
                ReadProjection::Computed { key, expected } => {
                    let key_read = self.child(reads[index + 1], *key, work)?;
                    let (record, _) = self.observation(key_read, work)?;
                    let value = &self
                        .expressions
                        .get(record.id.0 as usize)
                        .ok_or(SourceTypesError::MissingNode)?
                        .value;
                    match expected {
                        StaticCoordinate::Label(label) => {
                            work.text(label)?;
                            if let Some(StaticCoordinate::Label(actual)) = &value.static_coordinate
                            {
                                work.text(actual)?;
                            }
                            require(value.static_coordinate.as_ref() == Some(expected))?;
                            TypeProjection::Field(label.clone())
                        }
                        StaticCoordinate::Index(index) => {
                            require(value.constant == Some(Constant::Integer(*index)))?;
                            TypeProjection::Tuple(
                                u32::try_from(*index)
                                    .map_err(|_| SourceTypesError::MissingProjection)?,
                            )
                        }
                    }
                }
            };
            steps.push(projection);
        }
        let depth = self.unwrap_depth(outer, work)?;
        if view == SourceRead::Received && depth == 1 {
            steps.push(TypeProjection::OptionalPayload);
        }
        Ok(SourceProjection {
            root: root.id,
            steps,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn computed_literal_paths_require_their_own_actual_key_value_and_child() {
        let source = ril_test::case_source(
            "tests/regressions/source-observations.ril::optional-projection-paths-pointer64",
        );
        let program = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap();
        let facts = program.facts();
        let hir = facts.semantic_hir.as_deref().unwrap();
        for (name, expected) in [
            ("computed", TypeProjection::Field("items".into())),
            ("selected", TypeProjection::Tuple(0)),
        ] {
            let row = facts
                .binding_sources
                .iter()
                .find(|row| facts.bindings[row.binding].name == name)
                .unwrap();
            let record = &facts.evaluations[row.initializer.expression];
            let identity = record.identity.unwrap();
            let occurrence = ProjectionOccurrence {
                identity,
                context: record.context,
                cause: facts.expressions[row.initializer.expression].value.cause,
            };
            let plan = projection_path(hir, identity.source, &mut WorkLimit::new(4096))
                .unwrap()
                .unwrap();
            let ExprKind::ComputedField { key, .. } = hir.expression(identity.source).unwrap().kind
            else {
                panic!("computed Source fixture lost its original key");
            };
            let receipts = ProjectionReceipts::from_facts(facts);
            let key_read = receipts
                .child(occurrence, key, &mut WorkLimit::new(16384))
                .unwrap();
            let key_index = receipts
                .observation(key_read, &mut WorkLimit::new(16384))
                .unwrap()
                .0
                .id
                .0 as usize;
            let projection = receipts
                .project(
                    &plan,
                    occurrence,
                    SourceRead::Received,
                    &mut WorkLimit::new(16384),
                )
                .unwrap();
            assert_eq!(
                projection.steps,
                [TypeProjection::OptionalPayload, expected]
            );
            for mutation in 0..2 {
                let mut changed = facts.clone();
                if mutation == 0 {
                    changed.activations[key_read.identity.activation.0 as usize].parent = None;
                } else if name == "computed" {
                    changed.expressions[key_index].value.static_coordinate =
                        Some(StaticCoordinate::Label("other".into()));
                } else {
                    changed.expressions[key_index].value.constant = Some(Constant::Integer(1));
                }
                assert!(
                    ProjectionReceipts::from_facts(&changed)
                        .project(
                            &plan,
                            occurrence,
                            SourceRead::Received,
                            &mut WorkLimit::new(16384)
                        )
                        .is_err(),
                    "{name}: key mutation {mutation} supplied a different Source path"
                );
            }
        }
    }

    #[test]
    fn bounded_projection_uses_the_actual_base_read_without_expanding_the_outer_read_twice() {
        let source = ril_test::case_source(
            "tests/regressions/source-observations.ril::optional-projection-paths-pointer64",
        );
        let program = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap();
        let facts = program.facts();
        let row = facts
            .binding_sources
            .iter()
            .find(|row| facts.bindings[row.binding].name == "field")
            .unwrap();
        let record = &facts.evaluations[row.initializer.expression];
        let fact = &facts.expressions[row.initializer.expression];
        let hir = facts.semantic_hir.as_deref().unwrap();
        let identity = record.identity.unwrap();
        assert!(projection_path(hir, identity.source, &mut WorkLimit::new(0)).is_err());
        let plan = projection_path(hir, identity.source, &mut WorkLimit::new(4096))
            .unwrap()
            .unwrap();
        let occurrence = ProjectionOccurrence {
            identity,
            context: record.context,
            cause: fact.value.cause,
        };
        let receipts = ProjectionReceipts::from_facts(facts);
        assert!(
            receipts
                .project(
                    &plan,
                    occurrence,
                    SourceRead::Received,
                    &mut WorkLimit::new(0)
                )
                .is_err()
        );
        let raw = receipts
            .project(
                &plan,
                occurrence,
                SourceRead::Raw,
                &mut WorkLimit::new(16384),
            )
            .unwrap();
        let received = receipts
            .project(
                &plan,
                occurrence,
                SourceRead::Received,
                &mut WorkLimit::new(16384),
            )
            .unwrap();
        assert_eq!(
            raw.steps,
            [
                TypeProjection::OptionalPayload,
                TypeProjection::Field("items".into())
            ]
        );
        assert_eq!(raw.steps, received.steps);
        assert_eq!(
            facts.expressions[raw.root.0 as usize].source_id,
            Some(plan.root())
        );
        let mut changed = facts.clone();
        let base = changed.evaluations[raw.root.0 as usize].identity.unwrap();
        changed.activations[base.activation.0 as usize].parent = None;
        assert!(
            ProjectionReceipts::from_facts(&changed)
                .project(
                    &plan,
                    occurrence,
                    SourceRead::Received,
                    &mut WorkLimit::new(16384),
                )
                .is_err()
        );
    }
}
