//! A stored graph is a retained view. An independent read still authenticates
//! the declaration or the actual initializer that admitted that view.
use super::*;
use crate::sema::source_types::projection_receipts;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct AdmissionKey {
    binding: usize,
    declaration: ril_compiler_core::ids::PatternId,
    introducer: ril_compiler_core::ids::PatternId,
    initializer: ril_compiler_core::ids::EvaluationOccurrenceId,
    birth: crate::sema::application_effect::OccurrenceIdentity,
    allocation_epoch: usize,
    scope: crate::sema::facts::ScopeId,
    context: InvocationContext,
    environment: crate::sema::context::FrozenEnvId,
}

/// A memo of pure derivations in one immutable Replay. Claims, physical reads
/// and admission decisions are never cached. SourceQuery admission surrounds
/// both a hit and the original computation, so a hit cannot hide a cycle.
#[derive(Default)]
pub(in crate::sema::record_bound_validation) struct StorageAdmissions {
    graphs: std::cell::RefCell<BTreeMap<AdmissionKey, OriginalSource>>,
}

fn admission_work(work: &mut usize, amount: usize) -> Check {
    match work.checked_sub(amount) {
        Some(remaining) => {
            *work = remaining;
            Ok(())
        }
        None => {
            *work = 0;
            Err("stored Source derivation memo work exhausted".into())
        }
    }
}

impl StorageAdmissions {
    fn get(&self, key: &AdmissionKey, work: &mut usize) -> Check<Option<OriginalSource>> {
        let graphs = self.graphs.borrow();
        admission_work(work, 3 + graphs.len().checked_ilog2().unwrap_or(0) as usize)?;
        Ok(graphs.get(key).cloned())
    }

    fn insert(&self, key: AdmissionKey, graph: &OriginalSource, work: &mut usize) -> Check {
        let mut graphs = self.graphs.borrow_mut();
        admission_work(work, 3 + graphs.len().checked_ilog2().unwrap_or(0) as usize)?;
        graphs.insert(key, graph.clone());
        Ok(())
    }
}

impl Replay<'_> {
    pub(super) fn authenticate_storage_read(
        &self,
        observation: usize,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
    ) -> Check {
        *work = work
            .checked_sub(3)
            .ok_or("stored Source admission work exhausted")?;
        let fact = self
            .facts
            .expressions
            .get(observation)
            .ok_or("stored Source read is absent")?;
        let id = *fact
            .value
            .sources
            .first()
            .ok_or("stored Source read has no binding")?;
        require(
            fact.value.sources.len() == 1,
            "stored Source read joined different bindings",
        )?;
        let binding = self
            .facts
            .bindings
            .get(id)
            .ok_or("stored Source binding is absent")?;
        if binding.parameter {
            // The existing parameter path reconstructs its actual entry and
            // original formal header before returning the graph.
            return Ok(());
        }
        *work = work
            .checked_sub(2 + self.storage_bindings.len().checked_ilog2().unwrap_or(0) as usize)
            .ok_or("stored Source receipt lookup work exhausted")?;
        let row = self
            .storage_bindings
            .get(&id)
            .copied()
            .ok_or("stored Source has no initializer receipt")?;
        if row.receiver.is_some() {
            let expected = self
                .pattern_receiver_source(row, sites, work)?
                .ok_or("pattern receiver has no original Source graph")?;
            let (stored, environment) = graph_sources::schema_work(work, |budget| {
                self.facts
                    .source_types
                    .binding_schema_if_known(id, None, budget)
            })?
            .ok_or("pattern receiver Source index is absent")?;
            let source = fact
                .source_id
                .ok_or("pattern receiver read has no original HIR")?;
            let hir = self
                .facts
                .semantic_hir
                .as_deref()
                .ok_or("pattern receiver read has no HIR")?;
            let path = graph_sources::schema_work(work, |budget| {
                projection_receipts::projection_path(hir, source, budget)
            })?
            .ok_or("pattern receiver read has no Name root")?;
            require(
                self.lexical
                    .as_ref()
                    .ok_or("pattern receiver read has no lexical index")?
                    .lookup(path.root(), work)
                    .map_err(|error| error.to_string())?
                    == binding.pattern,
                "pattern receiver read borrowed another lexical binder",
            )?;
            require(
                environment.id() == binding.typing_environment.id()
                    && graph_sources::schema_work(work, |budget| {
                        stored.equivalent_in(&expected.0, &environment, &expected.1, budget)
                    })?,
                "pattern receiver Source index differs from its original subject",
            )?;
            return Ok(());
        }
        let owner = row
            .context
            .owner
            .ok_or("stored Source initializer has no lexical owner")?;
        let declaration = sites.binding_site(owner, row.declaration, work)?;
        let syntax = declaration.binding;
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("stored Source has no original HIR")?;
        let original = hir
            .statement(declaration.statement)
            .ok_or("stored Source declaration HIR is absent")?;
        require(
            matches!(&original.kind, crate::hir::nodes::StmtKind::Binding { pattern, ty, value, .. }
            if *pattern == row.declaration && *ty == syntax.ty.as_ref().and_then(|ty| ty.hir_id)
                && Some(*value) == syntax.value.hir_id),
            "stored Source declaration differs from canonical HIR",
        )?;
        require(
            row.binding == id
                && row.activation == binding.owner
                && row.context == binding.context
                && row.declared == syntax.ty.is_some(),
            "stored Source changed its binding, origin or declaration environment",
        )?;
        let initializer = self
            .facts
            .expressions
            .get(row.initializer.expression)
            .ok_or("stored Source initializer is absent")?;
        let birth = self
            .facts
            .evaluations
            .get(row.initializer.expression)
            .ok_or("stored Source initializer has no physical occurrence")?;
        require(
            binding.birth.is_some()
                && birth.identity == binding.birth
                && birth.id.0 as usize == row.initializer.expression
                && birth.scope == row.activation
                && birth.context == row.context
                && birth.allocation_epoch == row.initializer.allocation_epoch
                && initializer.allocation_epoch == row.initializer.allocation_epoch
                && initializer.source_id == syntax.value.hir_id
                && birth
                    .identity
                    .is_some_and(|identity| Some(identity.source) == syntax.value.hir_id),
            "stored Source borrowed another initializer occurrence",
        )?;
        *work = work
            .checked_sub(initializer.value.sources.len())
            .ok_or("stored Source origin work exhausted")?;
        require(
            initializer.value.ty != Ty::Never
                && initializer.value.sources.iter().all(|source| *source < id),
            "stored Source initializer is abrupt or cyclic",
        )?;
        let plan = hir
            .pattern_bindings(row.declaration, work)
            .map_err(|error| error.to_string())?;
        let mut selected = None;
        for leaf in plan {
            *work = work
                .checked_sub(1 + leaf.name.len().div_ceil(32) + binding.name.len().div_ceil(32))
                .ok_or("stored Source pattern work exhausted")?;
            if Some(leaf.pattern) == binding.pattern {
                require(
                    selected.is_none() && leaf.name == binding.name,
                    "stored Source binder differs from its original HIR pattern",
                )?;
                selected = Some(leaf.projection);
            }
        }
        let path = selected.ok_or("stored Source binder is absent from its original pattern")?;
        require(
            row.path == path,
            "stored Source changed its original binding projection",
        )?;
        let source = fact
            .source_id
            .ok_or("stored Source read has no original HIR")?;
        let path_plan = graph_sources::schema_work(work, |budget| {
            projection_receipts::projection_path(hir, source, budget)
        })?
        .ok_or("stored Source read has no original Name root")?;
        require(
            self.lexical
                .as_ref()
                .ok_or("stored Source has no lexical index")?
                .lookup(path_plan.root(), work)
                .map_err(|error| error.to_string())?
                == binding.pattern,
            "stored Source read borrowed a different lexical binder",
        )?;
        let (stored, environment) = graph_sources::schema_work(work, |budget| {
            self.facts
                .source_types
                .binding_schema_if_known(id, None, budget)
        })?
        .ok_or("stored Source index lost its original graph")?;
        require(
            !environment.is_poisoned() && environment.id() == binding.typing_environment.id(),
            "stored Source changed its frozen interpretation",
        )?;
        let key = AdmissionKey {
            binding: id,
            declaration: row.declaration,
            introducer: binding
                .pattern
                .ok_or("stored Source has no original introducer")?,
            initializer: birth.id,
            birth: birth
                .identity
                .ok_or("stored Source initializer has no occurrence")?,
            allocation_epoch: birth.allocation_epoch,
            scope: birth.scope,
            context: birth.context,
            environment: environment.id(),
        };
        let _entered = self
            .source_query
            .enter(crate::sema::source_query::QueryKind::Source, birth.id, work)
            .map_err(|error| error.to_string())?;
        let (expected, original_environment) = if let Some(graph) =
            self.storage_admissions.get(&key, work)?
        {
            graph
        } else {
            let (root, original_environment) = if let Some(header) = &syntax.ty {
                let scope = self.lambda_input_scope(owner, work)?;
                self.source_type_header(header, &scope, binding.typing_environment.clone(), work)?
            } else {
                self.original_observed_source_schema_with_work(
                    &syntax.value,
                    row.initializer.expression,
                    row.context,
                    sites,
                    work,
                )?
                .ok_or("stored Source initializer has no original graph")?
            };
            let expected = self
                .pattern_binding_projection(row, &root, &original_environment, work)?
                .ok_or("stored Source binder has no authenticated structural projection")?;
            require(
                !original_environment.is_poisoned(),
                "stored Source original environment is poisoned",
            )?;
            let graph = (expected, original_environment);
            self.storage_admissions.insert(key, &graph, work)?;
            graph
        };
        require(
            !original_environment.is_poisoned(),
            "stored Source original environment is poisoned",
        )?;
        if graph_sources::schema_work(work, |budget| expected.requires_environment(budget))? {
            require(
                original_environment.id() == environment.id(),
                "stored Source initializer changed its frozen interpretation",
            )?;
        }
        require(
            graph_sources::schema_work(work, |budget| stored.equivalent(&expected, budget))?,
            "stored Source index differs from its original admission",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckOptions, Session};

    fn facts() -> SemanticFacts {
        Session::with_options(
            ril_test::case_bytes("tests/stdlib/num.ril::numeric-callable-views").to_vec(),
            CheckOptions::default(),
        )
        .verify()
        .expect("the original callable views fixture must verify")
        .facts()
        .clone()
    }

    fn read(facts: &SemanticFacts, name: &str) -> usize {
        facts
            .copy_call_events
            .iter()
            .filter_map(|event| event.callee_expression)
            .find(|&token| {
                facts.expressions[token]
                    .value
                    .sources
                    .first()
                    .and_then(|id| facts.bindings.get(*id))
                    .is_some_and(|binding| binding.name == name)
            })
            .expect("the real fixture must call the requested stored view")
    }

    #[test]
    fn admission_memo_reuses_only_the_original_graph_and_keeps_cycle_and_work_checks() {
        let facts = facts();
        let mut work = 4_000_000;
        let replay = Replay::new_with_work(&facts, &mut work).unwrap();
        let sites =
            crate::sema::record_bound_validation::source_sites_base_with_work(&facts, &mut work)
                .unwrap();
        let token = read(&facts, "parse");
        replay
            .authenticate_storage_read(token, &sites, &mut work)
            .unwrap();
        let count = replay.storage_admissions.graphs.borrow().len();
        assert!(
            count > 0,
            "the first query must actually publish a graph derivation"
        );
        let before = work;
        replay
            .authenticate_storage_read(token, &sites, &mut work)
            .unwrap();
        let hit_work = before - work;
        assert!(
            hit_work > 0,
            "a memo hit still pays for the read, graph claim and lookup"
        );
        assert_eq!(replay.storage_admissions.graphs.borrow().len(), count);
        let mut exact = hit_work;
        replay
            .authenticate_storage_read(token, &sites, &mut exact)
            .unwrap();
        assert_eq!(exact, 0);
        assert!(
            replay
                .authenticate_storage_read(token, &sites, &mut 0)
                .is_err()
        );
        assert!(
            replay
                .authenticate_storage_read(token, &sites, &mut (hit_work - 1))
                .is_err()
        );

        let id = *facts.expressions[token].value.sources.first().unwrap();
        let initializer = replay.storage_bindings[&id].initializer.expression;
        let scope = replay
            .source_query
            .enter(
                crate::sema::source_query::QueryKind::Source,
                facts.evaluations[initializer].id,
                &mut work,
            )
            .unwrap();
        assert!(
            replay
                .authenticate_storage_read(token, &sites, &mut work)
                .is_err(),
            "a previously memoized graph cannot bypass its actual initializer's active query scope"
        );
        drop(scope);
        replay
            .authenticate_storage_read(token, &sites, &mut work)
            .unwrap();

        let other = read(&facts, "explicit_parse");
        replay
            .authenticate_storage_read(other, &sites, &mut work)
            .unwrap();
        let graphs = replay.storage_admissions.graphs.borrow();
        let first = graphs.keys().find(|key| key.binding == id).unwrap();
        let other_id = *facts.expressions[other].value.sources.first().unwrap();
        let second = graphs.keys().find(|key| key.binding == other_id).unwrap();
        assert_ne!(first.binding, second.binding);
        assert_ne!(first.introducer, second.introducer);
        assert_ne!(first.initializer, second.initializer);
        assert_ne!(first.birth, second.birth);
        for key in [first, second] {
            let row = &facts.evaluations[key.initializer.0 as usize];
            assert_eq!(Some(key.birth), row.identity);
            assert_eq!(
                key.environment,
                facts.bindings[key.binding].typing_environment.id()
            );
        }
        let mut other_environment = *first;
        other_environment.environment = FrozenEnvironment::default().id();
        assert!(
            replay
                .storage_admissions
                .get(&other_environment, &mut work)
                .unwrap()
                .is_none(),
            "an equal-looking new frozen environment cannot reuse the original graph derivation"
        );
    }

    #[test]
    fn admission_memo_does_not_authorize_another_facts_snapshot_or_environment() {
        let baseline = facts();
        let token = read(&baseline, "parse");
        let binding = *baseline.expressions[token].value.sources.first().unwrap();
        for mutation in 0..4 {
            let mut changed = baseline.clone();
            match mutation {
                0 => changed.binding_sources.retain(|row| row.binding != binding),
                1 => changed.builtin_source_observations.retain(|row| {
                    !matches!(
                        row.full_header,
                        crate::sema::builtin_sources::BuiltinDeclaration::Numeric(_)
                    )
                }),
                2 => changed.bindings[binding].typing_environment = FrozenEnvironment::default(),
                3 => {
                    changed.bindings[binding].birth = baseline
                        .bindings
                        .iter()
                        .find(|other| other.name == "explicit_parse")
                        .unwrap()
                        .birth
                }
                _ => unreachable!(),
            }
            let mut work = 4_000_000;
            let replay = Replay::new_with_work(&changed, &mut work).unwrap();
            let sites = crate::sema::record_bound_validation::source_sites_base_with_work(
                &changed, &mut work,
            )
            .unwrap();
            assert!(
                replay
                    .authenticate_storage_read(token, &sites, &mut work)
                    .is_err(),
                "an inferred read must reject missing or substituted evidence (mutation {mutation})"
            );
        }
    }
}
