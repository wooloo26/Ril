//! Numeric receiving views come from actual Source graphs and original headers.
use super::*;
use crate::sema::source_types::{
    SourcePath,
    projection_receipts::{self, ProjectionOccurrence, ProjectionReceipts, SourceRead},
};
use ril_compiler_core::ids::TypeExprId;

type BindingHeaderProjection = (Option<TypeExprId>, Vec<SourcePath>);

impl<'a, 'w> Replay<'a, 'w> {
    fn frozen_subject_source(
        &mut self,
        facts: &'a SemanticFacts,
        identity: OccurrenceIdentity,
        observation: EvaluationOccurrenceId,
    ) -> Result<(SourceSchema, FrozenEnvironment), SourceTypesError> {
        if self.sources.is_none() {
            self.sources = Some(
                crate::sema::record_bound_validation::OriginalOperandSources::new_with_work_in(
                    facts,
                    self.work,
                    self.query.clone(),
                )
                .map_err(SourceTypesError::InvalidEvidence)?,
            );
        }
        self.sources
            .as_ref()
            .ok_or(SourceTypesError::MissingNode)?
            .observed_with_work(identity.source, observation.0 as usize, self.work)
            .map_err(SourceTypesError::InvalidEvidence)?
            .0
            .ok_or(SourceTypesError::Unresolved)
    }
    pub(super) fn local_binding_header(
        &mut self,
        pattern: PatternId,
    ) -> Result<(Option<TypeExprId>, Vec<SourcePath>, ExprId), SourceTypesError> {
        if self.session.binding_statements != self.hir.statements().len()
            || self.session.binding_headers.is_none()
        {
            let hir = self.hir;
            let total = hir.statements().len();
            charge(
                self.work,
                total
                    .checked_sub(self.session.binding_statements)
                    .ok_or(SourceTypesError::Unresolved)?
                    + 1,
            )?;
            if self.session.binding_headers.is_none() {
                self.session.binding_headers = Some(BTreeMap::new());
            }
            for (_, statement) in hir.statements().skip(self.session.binding_statements) {
                if let hir::StmtKind::Binding {
                    pattern, ty, value, ..
                } = statement.kind
                {
                    let plan = hir
                        .pattern_bindings(pattern, self.work)
                        .map_err(hir_error)?;
                    charge(self.work, plan.len())?;
                    for leaf in plan {
                        if self
                            .session
                            .binding_headers
                            .as_mut()
                            .ok_or(SourceTypesError::MissingNode)?
                            .insert(leaf.pattern, (ty, leaf.projection, value))
                            .is_some()
                        {
                            return Err(SourceTypesError::Unresolved);
                        }
                    }
                }
                self.session.binding_statements += 1;
            }
        }
        let (header, path, source) = self
            .session
            .binding_headers
            .as_ref()
            .and_then(|headers| headers.get(&pattern))
            .ok_or(SourceTypesError::MissingNode)?;
        let path = path.as_ref().ok_or(SourceTypesError::MissingProjection)?;
        charge(self.work, path.len() + 2)?;
        for step in path {
            if let SourcePath::Field(name) = step {
                charge(self.work, name.len())?;
            }
        }
        Ok((*header, path.clone(), *source))
    }

    pub(super) fn graph_work<R>(
        &mut self,
        query: impl FnOnce(&mut WorkLimit) -> Result<R, SourceTypesError>,
    ) -> Result<R, SourceTypesError> {
        let mut work = WorkLimit::new(*self.work);
        let result = query(&mut work);
        *self.work = work.remaining();
        result
    }

    fn type_schema(&mut self, header: TypeExprId) -> Result<SourceSchema, SourceTypesError> {
        charge(self.work, 1)?;
        if let Some(schema) = self.session.headers.get(&header) {
            return Ok(schema.clone());
        }
        let hir = self.hir;
        if self.session.lexical.is_none() {
            self.session.lexical =
                Some(crate::hir::lexical::LexicalBindings::new(hir, self.work).map_err(hir_error)?);
        }
        let mut budget = WorkLimit::new(*self.work);
        let schema = crate::sema::source_types::declarations::type_schema_with_lexical(
            header,
            hir,
            self.session
                .lexical
                .as_ref()
                .ok_or(SourceTypesError::MissingNode)?,
            &mut budget,
        );
        *self.work = budget.remaining();
        let schema = schema?;
        charge(self.work, 2)?;
        self.session.headers.insert(header, schema.clone());
        Ok(schema)
    }

    fn header_projection(
        &mut self,
        root: PatternId,
        header: Option<TypeExprId>,
        binding: &crate::sema::model::BindingInfo,
    ) -> Result<Option<BindingHeaderProjection>, SourceTypesError> {
        let plan = self
            .hir
            .pattern_bindings(root, self.work)
            .map_err(hir_error)?;
        charge(self.work, plan.len())?;
        for leaf in plan {
            charge(self.work, 1 + leaf.name.len() + binding.name.len())?;
            if binding.pattern == Some(leaf.pattern) && binding.name == leaf.name {
                return Ok(Some((
                    header,
                    leaf.projection.ok_or(SourceTypesError::MissingProjection)?,
                )));
            }
        }
        Ok(None)
    }

    fn binding_header(
        &mut self,
        binding: &crate::sema::model::BindingInfo,
    ) -> Result<BindingHeaderProjection, SourceTypesError> {
        let hir = self.hir;
        let pattern = binding.pattern.ok_or(SourceTypesError::MissingNode)?;
        let owner = hir
            .pattern(pattern)
            .ok_or(SourceTypesError::MissingNode)?
            .info
            .owner;
        if binding.parameter {
            let parameters = match owner {
                hir::LexicalOwner::Declaration(id) => {
                    let hir::StmtKind::Function(function) =
                        &hir.statement(id).ok_or(SourceTypesError::MissingNode)?.kind
                    else {
                        return Err(SourceTypesError::Unresolved);
                    };
                    &function.parameters
                }
                hir::LexicalOwner::Lambda(id) => {
                    let hir::ExprKind::Lambda { parameters, .. } = &hir
                        .expression(id)
                        .ok_or(SourceTypesError::MissingNode)?
                        .kind
                    else {
                        return Err(SourceTypesError::Unresolved);
                    };
                    parameters
                }
                _ => return Err(SourceTypesError::Unresolved),
            };
            charge(self.work, parameters.len())?;
            for parameter in parameters {
                if let Some(header) =
                    self.header_projection(parameter.pattern, parameter.ty, binding)?
                {
                    return Ok(header);
                }
            }
        } else {
            let (header, path, _) = self.local_binding_header(pattern)?;
            return Ok((header, path));
        }
        Err(SourceTypesError::MissingNode)
    }

    fn binding_schema(
        &mut self,
        observation: EvaluationOccurrenceId,
        depth: usize,
    ) -> Result<(SourceSchema, FrozenEnvironment), SourceTypesError> {
        let record = self.record(observation)?;
        let identity = record.identity.ok_or(SourceTypesError::MissingNode)?;
        let hir::ExprKind::Name(name) = &self
            .hir
            .expression(identity.source)
            .ok_or(SourceTypesError::MissingNode)?
            .kind
        else {
            return Err(SourceTypesError::Unresolved);
        };
        let value = &self.facts.expressions[observation.0 as usize].value;
        if value.sources.len() != 1 {
            return Err(SourceTypesError::Unresolved);
        }
        let id = *value.sources.first().ok_or(SourceTypesError::MissingNode)?;
        let binding = self
            .facts
            .bindings
            .get(id)
            .ok_or(SourceTypesError::MissingNode)?;
        charge(self.work, 2 + name.len() + binding.name.len())?;
        if binding.name != *name
            || binding.owner != record.scope
            || binding.context != record.context
        {
            return Err(SourceTypesError::Unresolved);
        }
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
            != binding.pattern
        {
            return Err(SourceTypesError::Unresolved);
        }
        let types = self.facts.source_types;
        let (schema, environment) = self
            .graph_work(|work| types.binding_schema(id, work))?
            .ok_or(SourceTypesError::Unresolved)?;
        if environment.is_poisoned() || environment.id() != binding.typing_environment.id() {
            return Err(SourceTypesError::Unresolved);
        }
        let (header, path) = self.binding_header(binding)?;
        let original = if let Some(header) = header {
            let root = self.type_schema(header)?;
            self.graph_work(|work| root.project_steps(&path, work))?
        } else {
            if binding.parameter || !path.is_empty() {
                return Err(SourceTypesError::Unresolved);
            }
            let birth = binding.birth.ok_or(SourceTypesError::MissingNode)?;
            if self
                .local_binding_header(binding.pattern.ok_or(SourceTypesError::MissingNode)?)?
                .2
                != birth.source
            {
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
            self.subject_schema(origin, depth + 1)?.0
        };
        let equivalent = self.graph_work(|work| schema.equivalent(&original, work))?;
        if !equivalent {
            return Err(SourceTypesError::Unresolved);
        }
        Ok((schema, environment))
    }

    pub(super) fn subject_schema(
        &mut self,
        observation: EvaluationOccurrenceId,
        depth: usize,
    ) -> Result<(SourceSchema, FrozenEnvironment), SourceTypesError> {
        charge(self.work, 2)?;
        if depth >= 128 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        if let Some(schema) = self.schemas.get(&observation) {
            return Ok(schema.clone());
        }
        let record = self.record(observation)?;
        let identity = record.identity.ok_or(SourceTypesError::MissingNode)?;
        if let Some(packet) = self.facts.subject
            && packet.observation == Some(observation.0 as usize)
        {
            if packet.identity != Some(identity)
                || packet.birth_context != Some(record.context)
                || packet.allocation_epoch != record.allocation_epoch
            {
                return Err(SourceTypesError::Unresolved);
            }
            charge(self.work, 2)?;
            let source = packet
                .input_source()?
                .as_ref()
                .ok_or(SourceTypesError::Unresolved)?;
            if source.1.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            self.schemas.insert(observation, source.clone());
            return Ok(source.clone());
        }
        let hir = self.hir;
        let node = hir
            .expression(identity.source)
            .ok_or(SourceTypesError::MissingNode)?;
        if let Some(facts) = self.facts.frozen
            && !matches!(
                self.facts.expressions[observation.0 as usize].value.ty,
                Ty::NumericHole(_)
            )
            && !self.session.uses_by_occurrence.contains_key(&identity)
        {
            let source = self.frozen_subject_source(facts, identity, observation)?;
            charge(self.work, 2)?;
            self.schemas.insert(observation, source.clone());
            return Ok(source);
        }
        let plan = self
            .graph_work(|work| projection_receipts::projection_path(hir, identity.source, work))?;
        let (schema, environment) = if let Some(plan) = plan {
            let receipts = ProjectionReceipts {
                activations: self.facts.activations,
                evaluations: self.facts.evaluations,
                expressions: self.facts.expressions,
                witnesses: self.facts.witnesses,
                explanations: self.facts.explanations,
                open: self.facts.open,
            };
            let occurrence = ProjectionOccurrence {
                identity,
                context: record.context,
                cause: self.facts.expressions[observation.0 as usize].value.cause,
            };
            let projection = self.graph_work(|work| {
                receipts.project(&plan, occurrence, SourceRead::Received, work)
            })?;
            let (root, environment) = self.binding_schema(projection.root, depth)?;
            let schema = self.graph_work(|work| root.project_steps(&projection.steps, work))?;
            (schema, environment)
        } else if let Some(use_id) = self
            .session
            .uses_by_occurrence
            .get(&identity)
            .copied()
            .flatten()
        {
            let use_ = self
                .facts
                .numeric_uses
                .get(use_id.0 as usize)
                .ok_or(SourceTypesError::MissingNode)?;
            let resolution = self.hole(use_.hole, depth + 1)?;
            let scalar = crate::sema::evaluated::numeric_source_scalar(resolution.number_type);
            (
                self.graph_work(|work| SourceSchema::scalar(scalar, None, work))?,
                FrozenEnvironment::default(),
            )
        } else if let hir::ExprKind::Record {
            ty: Some(header), ..
        } = &node.kind
        {
            (self.type_schema(*header)?, FrozenEnvironment::default())
        } else if let Some(facts) = self.facts.frozen {
            self.frozen_subject_source(facts, identity, observation)?
        } else {
            return Err(SourceTypesError::Unresolved);
        };
        if environment.is_poisoned() {
            return Err(SourceTypesError::Unresolved);
        }
        charge(self.work, 2)?;
        self.schemas
            .insert(observation, (schema.clone(), environment.clone()));
        Ok((schema, environment))
    }

    pub(super) fn project_pattern_schema(
        &mut self,
        mut schema: SourceSchema,
        path: &[PatternStep],
    ) -> Result<SourceSchema, SourceTypesError> {
        for step in path {
            charge(self.work, 1)?;
            let source = match step {
                PatternStep::Tuple(index) => SourcePath::Tuple(
                    u32::try_from(*index).map_err(|_| SourceTypesError::MissingProjection)?,
                ),
                PatternStep::Field(name) => {
                    charge(self.work, name.len())?;
                    SourcePath::Field(name.clone())
                }
                PatternStep::Constructor(name)
                    if matches!(name.as_str(), "Some" | "Prelude::Some") =>
                {
                    SourcePath::OptionalPayload
                }
                PatternStep::Constructor(name) if matches!(name.as_str(), "Ok" | "Prelude::Ok") => {
                    SourcePath::ResultSuccess
                }
                PatternStep::Constructor(name)
                    if matches!(name.as_str(), "Err" | "Prelude::Err") =>
                {
                    SourcePath::ResultError
                }
                PatternStep::Constructor(name) => {
                    charge(self.work, name.len() + 1)?;
                    let constructor = self
                        .facts
                        .constructors
                        .get(name)
                        .ok_or(SourceTypesError::MissingNode)?;
                    let view = constructor.source.ok_or(SourceTypesError::Unresolved)?;
                    let types = self.facts.source_types;
                    let (owner, environment) =
                        self.graph_work(|work| types.view_schema(view, work))?;
                    if environment.is_poisoned()
                        || environment.id() != constructor.typing_environment.id()
                        || !self.graph_work(|work| owner.equivalent(&schema, work))?
                    {
                        return Err(SourceTypesError::Unresolved);
                    }
                    let header = constructor
                        .payload_syntax
                        .as_ref()
                        .and_then(|syntax| syntax.hir_id)
                        .ok_or(SourceTypesError::MissingNode)?;
                    schema = self.type_schema(header)?;
                    continue;
                }
            };
            schema = self.graph_work(|work| schema.project_steps(&[source], work))?;
        }
        Ok(schema)
    }
}
