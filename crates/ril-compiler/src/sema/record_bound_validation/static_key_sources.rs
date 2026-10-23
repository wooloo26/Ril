//! A value Name of a bound Key keeps the original product's scalar carrier.
use super::*;

impl Replay<'_> {
    pub(super) fn original_key_name_source_schema(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        observation: usize,
        work: &mut usize,
    ) -> Check<Option<OriginalSource>> {
        use crate::sema::source_types::declarations::{HeaderContext, key_carrier_source};
        let ExprKind::Name(name) = &expression.kind else {
            return Ok(None);
        };
        if !value.sources.is_empty() {
            return Ok(None);
        }
        let source = expression.hir_id.ok_or("Key Name lost its original HIR")?;
        let lexical = self
            .lexical
            .as_ref()
            .ok_or("Key Name has no original lexical index")?;
        let Some(parameter) = lexical
            .lookup_generic(source, work)
            .map_err(|error| format!("Key Name lexical identity: {error}"))?
        else {
            return Ok(None);
        };
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("Key Name has no original HIR")?;
        let generic = hir
            .generic(parameter)
            .ok_or("Key Name has no original generic declaration")?;
        if !generic
            .bound
            .and_then(|id| hir.type_expression(id))
            .is_some_and(|bound| matches!(bound.kind, crate::hir::nodes::TypeKind::KeyOf(_)))
        {
            require(
                !matches!(value.ty, Ty::StaticKey(_)),
                "Key Name lost its original coordinate sort",
            )?;
            return Ok(None);
        }
        source_scan_work(work, 3 + name.len().div_ceil(32))?;
        self.original_source_root(expression, value, context, Some(observation), work)?;
        require(hir.expression(source).is_some_and(|node| matches!(&node.kind, crate::hir::nodes::ExprKind::Name(actual) if actual == name)), "Key Name changed its original lexical syntax")?;
        let record = self
            .facts
            .evaluations
            .get(observation)
            .ok_or("Key Name has no actual read")?;
        self.storage_activation(context, record.scope, work)?;
        let environment = super::graph_sources::schema_work(work, |budget| {
            self.facts.source_types.environment(
                record
                    .environment
                    .ok_or(crate::sema::source_types::SourceTypesError::MissingNode)?,
                budget,
            )
        })?;
        source_scan_work(work, generic.name.len().div_ceil(32) + 1)?;
        let identity = environment
            .generic_context
            .get(&generic.name)
            .ok_or("Key Name lost its frozen binder UID")?;
        source_scan_work(work, identity.len().div_ceil(32))?;
        require(
            matches!(&value.ty, Ty::StaticKey(actual) if actual == identity)
                && value.static_coordinate.as_ref()
                    == environment.static_key_arguments.get(identity),
            "Key Name changed its original sort or frozen coordinate",
        )?;
        let schema = super::graph_sources::schema_work(work, |budget| {
            key_carrier_source(
                parameter,
                identity,
                HeaderContext {
                    declarations: &self.facts.external_type_declarations,
                    program: self
                        .facts
                        .source_program
                        .as_deref()
                        .ok_or(crate::sema::source_types::SourceTypesError::MissingNode)?,
                    hir,
                    lexical,
                    binders: &environment.generic_context,
                    functions: &self.facts.functions,
                    generic_binders: &self.facts.generic_binders,
                    layout: self
                        .facts
                        .target_layout
                        .ok_or(crate::sema::source_types::SourceTypesError::MissingNode)?,
                },
                budget,
            )
        })?;
        Ok(Some((schema, environment)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::source_types::{SourceScalar, WorkLimit};
    use crate::sema::source_types_ref::SourceTypesRef;

    #[test]
    fn real_key_names_keep_the_original_carrier_and_independent_static_duties() {
        let original = ril_test::case_source("tests/conformance/static.ril::accept-key-membership");
        for uppercase in [false, true] {
            let source = if uppercase {
                original.replace("record.(key)", "record.(K)")
            } else {
                original.into()
            };
            for layout in ["pointer32", "pointer64"] {
                let program = crate::Session::with_options(
                    source.as_bytes().to_vec(),
                    crate::CheckOptions {
                        target: layout.into(),
                        ..Default::default()
                    },
                )
                .verify()
                .unwrap_or_else(|error| panic!("uppercase={uppercase}/{layout}: {error:?}"));
                let facts = program.facts();
                let hir = facts.semantic_hir.as_deref().unwrap();
                let mut work = 4_000_000;
                let query =
                    crate::sema::record_bound_validation::OriginalOperandSources::new_with_work(
                        facts, &mut work,
                    )
                    .unwrap();
                let mut checked = 0;
                for (observation, fact) in facts.expressions.iter().enumerate() {
                    let Some(source) = fact.source_id else {
                        continue;
                    };
                    let crate::hir::nodes::ExprKind::Name(name) =
                        &hir.expression(source).unwrap().kind
                    else {
                        continue;
                    };
                    if !matches!(fact.value.ty, Ty::StaticKey(_))
                        || name != if uppercase { "K" } else { "key" }
                    {
                        continue;
                    }
                    checked += 1;
                    let mut budget = WorkLimit::new(16384);
                    let captured = fact
                        .value
                        .packet()
                        .birth_source(SourceTypesRef::Frozen(&facts.source_types), &mut budget)
                        .unwrap();
                    let captured = captured
                        .schema
                        .expect("a real Key value has a scalar Source carrier");
                    assert_eq!(
                        captured.scalar_representation(&mut budget).unwrap(),
                        Some(SourceScalar::Str)
                    );
                    assert!(captured.binder_identities(&mut budget).unwrap().is_empty());
                    let (expected, _) = query
                        .observed_with_work(source, observation, &mut work)
                        .unwrap()
                        .0
                        .unwrap();
                    assert!(captured.equivalent(&expected, &mut budget).unwrap());
                    assert!(
                        query
                            .observed_with_work(source, observation, &mut 0)
                            .is_err()
                    );
                    if uppercase {
                        for mutation in 0..3 {
                            let mut changed = facts.clone();
                            let function = changed
                                .functions
                                .iter_mut()
                                .find(|function| {
                                    function
                                        .syntax
                                        .generics
                                        .iter()
                                        .any(|parameter| parameter.name == "K")
                                })
                                .unwrap();
                            match mutation {
                                0 => {
                                    function
                                        .syntax
                                        .generics
                                        .iter_mut()
                                        .find(|parameter| parameter.name == "K")
                                        .unwrap()
                                        .hir_id = None
                                }
                                1 => {
                                    let bound = function
                                        .syntax
                                        .generics
                                        .iter_mut()
                                        .find(|parameter| parameter.name == "K")
                                        .unwrap()
                                        .bound
                                        .as_mut()
                                        .unwrap();
                                    let ril_syntax::ast::TypeKind::KeyOf(base) = &bound.kind else {
                                        unreachable!()
                                    };
                                    bound.kind = base.kind.clone();
                                }
                                2 => {
                                    let identity =
                                        changed.evaluations[observation].identity.unwrap();
                                    changed.evaluations[observation].scope =
                                        crate::sema::facts::ScopeId(0);
                                    changed.activations[identity.activation.0 as usize].scope =
                                        crate::sema::facts::ScopeId(0);
                                }
                                _ => unreachable!(),
                            }
                            assert!(crate::sema::record_bound_validation::OriginalOperandSources::new_with_work(&changed, &mut 4_000_000)
                                .and_then(|query| query.observed_with_work(source, observation, &mut 4_000_000)).is_err(),
                                "Key source mutation {mutation} borrowed another declaration, sort or actual scope");
                        }
                    }
                }
                assert!(checked > 0, "the fixture must emit a real Key Name");
                assert!(!facts.static_key_checks.is_empty());
                let mut missing_membership = facts.clone();
                missing_membership.static_key_checks.clear();
                assert!(
                    crate::sema::validate::solved_facts(&missing_membership).is_err(),
                    "the scalar Source must not replace actual Key membership"
                );
            }
        }
    }
}
