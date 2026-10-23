//! Reconstruct a pattern receiver's Source from its real subject occurrence,
//! retaining the enclosing operation independently of each binding's birth.
use super::*;
use crate::sema::{
    context::FrozenEnvironment,
    source_types::{SourceSchema, WorkLimit},
    storage_sources::BindingSource,
};

fn charge(work: &mut usize, amount: usize) -> Check {
    *work = work
        .checked_sub(amount)
        .ok_or("pattern receiver replay exceeds its work bound")?;
    Ok(())
}

fn pattern_work<T>(
    work: &mut usize,
    query: impl FnOnce(&mut WorkLimit) -> Result<T, crate::sema::source_types::SourceTypesError>,
) -> Check<T> {
    let mut budget = WorkLimit::new(*work);
    let result = query(&mut budget);
    *work = budget.remaining();
    result.map_err(|error| error.to_string())
}

impl Replay<'_> {
    pub(super) fn parameter_pattern_slot(
        &self,
        binding: &crate::sema::model::BindingInfo,
        roots: impl IntoIterator<Item = ril_compiler_core::ids::PatternId>,
        work: &mut usize,
    ) -> Check<(usize, ril_compiler_core::ids::PatternId)> {
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("formal pattern has no original HIR")?;
        let introducer = binding
            .pattern
            .ok_or("formal pattern lost its original introducer")?;
        let mut selected = None;
        for (slot, root) in roots.into_iter().enumerate() {
            charge(work, 1)?;
            let member = pattern_work(work, |budget| {
                crate::sema::pattern_sources::contains_binding(
                    hir,
                    root,
                    introducer,
                    &binding.name,
                    budget,
                )
            })?;
            if member {
                require(
                    selected.replace((slot, root)).is_none(),
                    "formal pattern belongs to more than one parameter",
                )?;
            }
        }
        selected.ok_or_else(|| "formal pattern belongs to another original parameter".into())
    }

    pub(super) fn parameter_binding_projection(
        &self,
        binding: &crate::sema::model::BindingInfo,
        root: ril_compiler_core::ids::PatternId,
        source: &SourceSchema,
        environment: &FrozenEnvironment,
        work: &mut usize,
    ) -> Check<Option<SourceSchema>> {
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("formal projection has no original HIR")?;
        let lexical = self
            .lexical
            .as_ref()
            .ok_or("formal projection has no lexical index")?;
        let introducer = binding
            .pattern
            .ok_or("formal projection lost its original introducer")?;
        pattern_work(work, |budget| {
            crate::sema::pattern_sources::project_binding(
                source,
                environment,
                hir,
                lexical,
                &self.facts.constructors,
                root,
                introducer,
                &binding.name,
                budget,
            )
        })
    }

    pub(super) fn pattern_binding_projection(
        &self,
        row: &BindingSource,
        source: &SourceSchema,
        environment: &FrozenEnvironment,
        work: &mut usize,
    ) -> Check<Option<SourceSchema>> {
        charge(work, 3)?;
        let binding = self
            .facts
            .bindings
            .get(row.binding)
            .ok_or("pattern receiver binding is absent")?;
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("pattern receiver has no original HIR")?;
        let lexical = self
            .lexical
            .as_ref()
            .ok_or("pattern receiver has no lexical index")?;
        let mut budget = WorkLimit::new(*work);
        let result = crate::sema::pattern_sources::project_binding(
            source,
            environment,
            hir,
            lexical,
            &self.facts.constructors,
            row.declaration,
            binding
                .pattern
                .ok_or("pattern receiver has no introducer")?,
            &binding.name,
            &mut budget,
        );
        *work = budget.remaining();
        result.map_err(|error| error.to_string())
    }

    pub(super) fn pattern_receiver_source(
        &self,
        row: &BindingSource,
        sites: &super::explicit_named::SourceSites<'_>,
        work: &mut usize,
    ) -> Check<Option<(SourceSchema, FrozenEnvironment)>> {
        use crate::hir::nodes::ExprKind as HirExpr;
        use crate::sema::application_effect::ActivationKind;
        charge(work, 12)?;
        let receiver = row
            .receiver
            .ok_or("pattern receiver lost its operation occurrence")?;
        let binding = self
            .facts
            .bindings
            .get(row.binding)
            .ok_or("pattern receiver binding is absent")?;
        require(
            !row.declared
                && !binding.parameter
                && row.activation == binding.owner
                && row.context == binding.context,
            "pattern receiver changed its frame, context or declared role",
        )?;
        self.storage_activation(row.context, row.activation, work)?;
        let host = self
            .facts
            .activations
            .get(receiver.activation.0 as usize)
            .ok_or("pattern receiver host activation is absent")?;
        require(
            host.id == receiver.activation
                && host.source == Some(receiver.source)
                && host.kind == ActivationKind::Expression
                && host.scope == row.activation
                && host.context == row.context,
            "pattern receiver borrowed another host operation",
        )?;
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("pattern receiver has no original HIR")?;
        let original = hir
            .expression(receiver.source)
            .ok_or("pattern receiver host has no original syntax")?;
        let subject_id = match &original.kind {
            HirExpr::Match {
                value,
                arms,
                type_match: false,
            } => {
                charge(work, arms.len())?;
                require(
                    arms.iter()
                        .filter(|arm| arm.pattern == row.declaration)
                        .count()
                        == 1,
                    "pattern receiver borrowed another match arm",
                )?;
                *value
            }
            HirExpr::IfLet { pattern, value, .. } | HirExpr::WhileLet { pattern, value, .. } => {
                require(
                    *pattern == row.declaration,
                    "conditional receiver borrowed another pattern",
                )?;
                *value
            }
            _ => {
                return Err(
                    "pattern receiver does not belong to a binding condition or match".into(),
                );
            }
        };
        let subject = self
            .facts
            .expressions
            .get(row.initializer.expression)
            .ok_or("pattern receiver subject is absent")?;
        let record = self
            .facts
            .evaluations
            .get(row.initializer.expression)
            .ok_or("pattern receiver subject has no actual evaluation")?;
        let identity = record
            .identity
            .ok_or("pattern receiver subject has no actual identity")?;
        let activation = self
            .facts
            .activations
            .get(identity.activation.0 as usize)
            .ok_or("pattern receiver subject lost its activation")?;
        require(
            record.id.0 as usize == row.initializer.expression
                && identity.source == subject_id
                && subject.source_id == Some(subject_id)
                && activation.id == identity.activation
                && activation.source == Some(subject_id)
                && activation.result == Some(record.id)
                && activation.parent == Some(receiver.activation)
                && activation.kind == ActivationKind::Expression
                && activation.context == row.context
                && record.context == row.context
                && activation.scope == row.activation
                && record.scope == row.activation
                && record.allocation_epoch == row.initializer.allocation_epoch
                && subject.allocation_epoch == row.initializer.allocation_epoch
                && binding.birth == Some(identity)
                && subject.value.ty != Ty::Never
                && subject
                    .value
                    .sources
                    .iter()
                    .all(|source| *source < row.binding),
            "pattern receiver borrowed another subject, completion, epoch or binding birth",
        )?;
        require(
            host.start_expression <= row.initializer.expression
                && host
                    .result
                    .is_some_and(|result| row.initializer.expression < result.0 as usize),
            "pattern receiver subject is outside its actual operation",
        )?;
        let plan = hir
            .pattern_bindings(row.declaration, work)
            .map_err(|error| error.to_string())?;
        charge(work, plan.len())?;
        let leaf = plan
            .iter()
            .find(|site| Some(site.pattern) == binding.pattern && site.name == binding.name)
            .ok_or("pattern receiver binder is absent from its original plan")?;
        require(
            row.path == leaf.projection,
            "pattern receiver changed its original structural path",
        )?;
        let subject_syntax = sites
            .expressions
            .get(&subject_id)
            .ok_or("pattern receiver subject lost its original AST")?;
        let _entered = self
            .source_query
            .enter(
                crate::sema::source_query::QueryKind::Source,
                record.id,
                work,
            )
            .map_err(|error| error.to_string())?;
        let Some((root, environment)) = self.original_observed_source_schema_with_work(
            subject_syntax,
            row.initializer.expression,
            row.context,
            sites,
            work,
        )?
        else {
            return Ok(None);
        };
        let projected = self.pattern_binding_projection(row, &root, &environment, work)?;
        if let Some(schema) = &projected {
            let mut budget = WorkLimit::new(*work);
            let sensitive = schema
                .requires_environment(&mut budget)
                .map_err(|error| error.to_string())?;
            *work = budget.remaining();
            require(
                !environment.is_poisoned()
                    && (!sensitive || environment.id() == binding.typing_environment.id()),
                "pattern receiver changed its original frozen interpretation",
            )?;
        }
        Ok(projected.map(|schema| (schema, environment)))
    }
}
