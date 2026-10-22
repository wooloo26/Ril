//! Independently replay the input of an original unannotated Name formal.
use super::*;
use crate::sema::scopes::ScopeOrigin;

impl Replay<'_> {
    pub(in crate::sema::record_bound_validation) fn inferred_closure_parameter_schema(
        &self,
        binding_id: usize,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
    ) -> Check<Option<Option<OriginalSource>>> {
        *work = work
            .checked_sub(1)
            .ok_or("inferred formal Source work exhausted")?;
        let binding = self
            .facts
            .bindings
            .get(binding_id)
            .ok_or("inferred formal binding is absent")?;
        if !binding.parameter {
            return Ok(None);
        }
        let Some(scope) = self.facts.scopes.get(&binding.owner) else {
            return Err("inferred formal receiver is absent".into());
        };
        let ScopeOrigin::Closure(id) = scope.origin else {
            return Ok(None);
        };
        let call = self
            .facts
            .closure_invocations
            .get(id.0 as usize)
            .ok_or("inferred formal entry is absent")?;
        let closure = self
            .facts
            .closures
            .get(call.closure)
            .ok_or("inferred formal object is absent")?;
        let site = closure
            .site
            .and_then(|id| self.facts.closure_sites.get(id.0 as usize))
            .ok_or("inferred formal site is absent")?;
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("inferred formal has no HIR")?;
        let original = hir
            .expression(site.source)
            .ok_or("inferred formal source is absent")?;
        let crate::hir::nodes::ExprKind::Lambda { parameters, .. } = &original.kind else {
            return Err("inferred formal source is not a lambda".into());
        };
        let pattern = binding
            .pattern
            .ok_or("lambda formal lost its original pattern")?;
        let pattern_node = hir
            .pattern(pattern)
            .ok_or("lambda formal pattern is absent")?;
        if let crate::hir::nodes::PatternKind::Name(name) = &pattern_node.kind {
            require(
                name == &binding.name,
                "lambda formal changed its original binder name",
            )?;
        }
        *work = work
            .checked_sub(parameters.len())
            .ok_or("inferred formal header work exhausted")?;
        let mut parameters = parameters.iter().enumerate().filter(|(_, parameter)| {
            binding.pattern == Some(parameter.pattern)
                && hir.pattern(parameter.pattern).is_some_and(|pattern|
                    matches!(&pattern.kind, crate::hir::nodes::PatternKind::Name(name) if name == &binding.name))
        });
        let Some((slot, parameter)) = parameters.next() else {
            let mut member = false;
            for parameter in match &original.kind {
                crate::hir::nodes::ExprKind::Lambda { parameters, .. } => parameters,
                _ => unreachable!(),
            } {
                let plan = hir
                    .pattern_bindings(parameter.pattern, work)
                    .map_err(|error| error.to_string())?;
                member |= plan
                    .iter()
                    .any(|site| site.pattern == pattern && site.name == binding.name);
            }
            require(member, "lambda formal belongs to another original receiver")?;
            return Ok(None);
        };
        require(
            parameters.next().is_none(),
            "inferred formal has ambiguous original parameters",
        )?;
        if parameter.ty.is_some() {
            return Ok(None);
        }
        require(
            call.id == id
                && call.activation == Some(binding.owner)
                && call.status == CopyInvocationStatus::Completed
                && binding.context.closure_invocation == Some(id)
                && binding.context.closure == Some(call.closure)
                && binding.context.owner == Some(CallableOwner::Lambda(site.id))
                && closure.hir_id == Some(site.source),
            "inferred formal borrowed another actual receiver or original header",
        )?;
        require(
            !binding.typing_environment.is_poisoned()
                && binding.typing_environment.id() == closure.contract.typing_environment.id(),
            "inferred formal changed its declaration's lexical environment",
        )?;
        let expected = self.closure_entry_source_schema_if_known(call, slot, sites, work, 0)?;
        let stored = super::graph_sources::schema_work(work, |budget| {
            self.facts
                .source_types
                .binding_schema_if_known(binding_id, None, budget)
        })?;
        match (&expected, &stored) {
            (None, None) => require(
                self.facts.source_types.validate_binding_schema(
                    binding_id,
                    None,
                    binding.typing_environment.id(),
                ),
                "unknown inferred formal changed its original admission",
            )?,
            (Some((expected, original_environment)), Some((schema, environment))) => {
                require(
                    !environment.is_poisoned()
                        && !original_environment.is_poisoned()
                        && self.facts.source_types.binding_environment(binding_id)
                            == Some(environment.id()),
                    "inferred formal changed its admitted Source environment",
                )?;
                let same = super::graph_sources::schema_work(work, |budget| {
                    Ok(schema.equivalent(expected, budget)?
                        && (!schema.requires_environment(budget)?
                            || original_environment.id() == environment.id()))
                })?;
                require(
                    same,
                    "inferred formal graph differs from its original physical entry",
                )?;
            }
            _ => return Err("inferred formal changed its original Source availability".into()),
        }
        Ok(Some(stored))
    }
}
