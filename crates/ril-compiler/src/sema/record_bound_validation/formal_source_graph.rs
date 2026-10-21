//! Named formal declarations supply type coordinates independently of loans.
//! Reading a Source graph neither requires readonly reception nor grants access.
use super::*;
use crate::sema::{
    context::FrozenEnvironment,
    scopes::ScopeOrigin,
    source_types::{SourceSchema, WorkLimit, declarations},
};

impl Replay<'_> {
    pub(super) fn parameter_declaration_schema(
        &self,
        root_ast: &Expr,
        binding: usize,
        context: crate::sema::effect_identity::InvocationContext,
        observation: usize,
        work: &mut WorkLimit,
    ) -> Check<Option<(SourceSchema, FrozenEnvironment)>> {
        work.charge(1).map_err(|error| error.to_string())?;
        let info = self
            .facts
            .bindings
            .get(binding)
            .ok_or("formal Source declaration binding is absent")?;
        if !info.parameter {
            return Ok(None);
        }
        let scope_record = self
            .facts
            .scopes
            .get(&info.owner)
            .ok_or("formal Source declaration has no actual receiver frame")?;
        let ScopeOrigin::Named(instance) = scope_record.origin else {
            // Operation arms can retain an enclosing Function owner in their
            // context. Their signatures come from the operation receiver.
            return Ok(None);
        };
        let Some(CallableOwner::Function(owner)) = info.context.owner else {
            return Err("named formal Source frame has another callable owner".into());
        };
        let ExprKind::Name(name) = &root_ast.kind else {
            return Err("formal Source declaration root is not an original Name".into());
        };
        let fact = self
            .facts
            .expressions
            .get(observation)
            .ok_or("formal Source declaration read is outside its arena")?;
        require(
            name == &info.name && fact.value.sources == BTreeSet::from([binding]),
            "formal Source declaration read borrowed another named binding",
        )?;
        let declaration =
            self.parameter_declaration_context(root_ast, &fact.value, context, Some(observation))?;
        require(
            declaration == info.context && declaration.invocation == Some(instance),
            "formal Source graph borrowed another named receiver activation",
        )?;
        let call = self
            .facts
            .copy_invocations
            .get(instance.0 as usize)
            .filter(|call| {
                call.id == instance
                    && call.target == owner
                    && call.status == CopyInvocationStatus::Completed
            })
            .ok_or("formal Source declaration has no completed actual named entry")?;
        let function = self.function(owner)?;
        work.charge(1 + function.syntax.parameters.len())
            .map_err(|error| error.to_string())?;
        let parameters: Vec<_> = function
            .syntax
            .parameters
            .iter()
            .enumerate()
            .filter(|(_, parameter)| {
                info.pattern.is_some()
                    && parameter.pattern.hir_id == info.pattern
                    && matches!(&parameter.pattern.kind, ril_syntax::ast::PatternKind::Name(actual) if actual == name)
            })
            .collect();
        let [(slot, parameter)] = parameters.as_slice() else {
            return Err("formal Source graph lost its unique original parameter header".into());
        };
        let syntax = parameter
            .ty
            .as_ref()
            .ok_or("named formal Source graph has no written type")?;
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("formal Source graph has no original HIR")?;
        let header = function
            .hir_id
            .and_then(|id| hir.statement(id))
            .ok_or("formal Source graph lost its original named declaration")?;
        let crate::hir::nodes::StmtKind::Function(header) = &header.kind else {
            return Err("formal Source graph declaration is not a named function".into());
        };
        require(
            header.parameters.get(*slot).is_some_and(|original| {
                Some(original.pattern) == info.pattern && original.ty == syntax.hir_id
            }),
            "formal Source graph header differs from the original HIR parameter",
        )?;
        let scope = self.scope(owner)?;
        let expected = self
            .input_parameter_source_key(syntax, &scope)?
            .map(|key| {
                let key = super::call_input_source::input_select_key(
                    &key,
                    &self.input_selected_keys(call)?,
                    0,
                )?;
                declarations::schema(&key, hir, work).map_err(|error| error.to_string())
            })
            .transpose()?;
        let stored = self
            .facts
            .source_types
            .binding_schema_if_known(binding, syntax.hir_id, work)
            .map_err(|error| error.to_string())?;
        require(
            self.facts.source_types.binding_environment(binding)
                == Some(info.typing_environment.id())
                && !info.typing_environment.is_poisoned(),
            "formal Source graph changed its original frozen interpretation",
        )?;
        match (stored, expected) {
            (None, None) => Ok(None),
            (Some((schema, environment)), Some(expected)) => {
                require(
                    environment.id() == info.typing_environment.id(),
                    "formal Source graph borrowed another declaration environment",
                )?;
                let schema = declarations::resolve_schema(&schema, hir, work)
                    .map_err(|error| error.to_string())?;
                require(
                    schema
                        .equivalent(&expected, work)
                        .map_err(|error| error.to_string())?,
                    "formal Source graph differs from its original selected header",
                )?;
                Ok(Some((schema, environment)))
            }
            _ => Err("formal Source graph changed its declared availability".into()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mutable_formal_source_graph_is_a_declaration_read_and_keeps_its_identity() {
        let source =
            ril_test::case_source("tests/conformance/provenance.ril::accept-runtime-index-overlap");
        let program = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap();
        let facts = program.facts();
        let sites = super::super::explicit_named::source_sites_base(facts).unwrap();
        let root = sites
            .bindings
            .iter()
            .find_map(|site| match &site.binding.value.kind {
                ExprKind::Field { base, .. } if matches!(&base.kind, ExprKind::Name(name) if name == "a") => Some(base.as_ref()),
                _ => None,
            })
            .unwrap();
        let (observation, fact) = facts
            .expressions
            .iter()
            .enumerate()
            .find(|(_, fact)| {
                fact.source_id == root.hir_id
                    && fact.value.permission == crate::sema::facts::Permission::Write
                    && fact.value.sources.len() == 1
            })
            .unwrap();
        let binding = *fact.value.sources.first().unwrap();
        let context = facts.evaluations[observation].context;
        let replay = Replay::new(facts).unwrap();
        assert!(
            replay
                .parameter_declaration_schema(
                    root,
                    binding,
                    context,
                    observation,
                    &mut WorkLimit::new(16384),
                )
                .unwrap()
                .is_some()
        );
        assert!(
            replay
                .parameter_declaration_schema(
                    root,
                    binding,
                    context,
                    observation,
                    &mut WorkLimit::new(0),
                )
                .is_err()
        );
        for mutation in 0..5 {
            let mut changed = facts.clone();
            match mutation {
                0 => changed.bindings[binding].typing_environment = Default::default(),
                1 => changed.source_types = Default::default(),
                2 => changed.bindings[binding].pattern = None,
                _ => {
                    let mut index = crate::sema::source_types::LiveSourceTypes::default();
                    let forged = ArgumentKey::Binder {
                        identity: "unrelated:forged".into(),
                        sort: StaticBinderSort::Type,
                    };
                    index
                        .record(
                            binding,
                            (mutation == 3).then_some(&forged),
                            facts.bindings[binding].typing_environment.clone(),
                        )
                        .unwrap();
                    changed.source_types = index.freeze();
                }
            }
            let result = Replay::new(&changed).and_then(|replay| {
                replay.parameter_declaration_schema(
                    root,
                    binding,
                    context,
                    observation,
                    &mut WorkLimit::new(16384),
                )
            });
            assert!(
                result.is_err(),
                "mutation {mutation} replaced a named formal declaration graph"
            );
        }
    }
}
