//! Replay foreign specialization from its original declaration and physical
//! Generic evaluation. Generated syntax and normalized argument caches cannot
//! establish their own source identity.
use super::{
    ExternalApplication, ExternalInstance, SemanticFacts,
    application_effect::{
        ActivationKind, EvaluationActivation, EvaluationRecord, OccurrenceIdentity,
    },
    model::{Callable, FunctionInfo},
};
use crate::{hir::nodes as h, static_eval};
use ril_compiler_core::ids::{
    ActivationEpochId, CallableOwner, DefinitionId, EvaluationOccurrenceId, ExprId, StmtId,
};
use ril_syntax::ast::{self, ExprKind};
use std::collections::{BTreeMap, BTreeSet, btree_map::Entry};

type Check<T = ()> = Result<T, String>;

fn require(condition: bool, message: &str) -> Check {
    condition.then_some(()).ok_or_else(|| message.into())
}

fn charge(work: &mut usize, units: usize) -> Check {
    *work = work
        .checked_sub(units)
        .ok_or("foreign instance replay exhausted its work bound")?;
    Ok(())
}

fn map_work(work: &mut usize, len: usize) -> Check {
    charge(work, 1 + len.checked_ilog2().unwrap_or(0) as usize)
}

fn admit(function: &ast::Function, work: &mut usize) -> Check {
    static_eval::charge_function_syntax_clone(function, work)
        .ok_or_else(|| "foreign generated signature exceeds its syntax work bound".into())
}

fn normalized_equal(left: &ast::TypeExpr, right: &ast::TypeExpr, work: &mut usize) -> Check<bool> {
    static_eval::charge_type_syntax_clone(left, work)
        .ok_or("foreign normalized argument exceeds its work bound")?;
    static_eval::charge_type_syntax_clone(right, work)
        .ok_or("foreign normalized argument exceeds its work bound")?;
    let left = static_eval::normalized_argument_key(left);
    let right = static_eval::normalized_argument_key(right);
    charge(work, left.len().div_ceil(32) + right.len().div_ceil(32))?;
    Ok(left == right)
}

fn failure(error: static_eval::ArgumentNormalizationError) -> String {
    match error {
        static_eval::ArgumentNormalizationError::Diagnostic(code, message) => {
            format!("foreign instance normalization rejected {code}: {message}")
        }
        static_eval::ArgumentNormalizationError::Unsupported(message) => message,
    }
}

#[derive(Clone, Copy)]
enum Child {
    One(EvaluationOccurrenceId),
    Duplicate,
}

struct Replay<'a, 'w> {
    facts: &'a SemanticFacts,
    hir: &'a h::HirProgram,
    work: &'w mut usize,
    children: BTreeMap<(ActivationEpochId, ExprId), Child>,
    instances: BTreeMap<usize, usize>,
    owners: BTreeMap<DefinitionId, Option<StmtId>>,
    covered: BTreeSet<OccurrenceIdentity>,
}

impl<'a> Replay<'a, '_> {
    fn index_application(&mut self, occurrence: OccurrenceIdentity) -> Check {
        charge(self.work, 1)?;
        let parent = self
            .facts
            .activations
            .get(occurrence.activation.0 as usize)
            .filter(|parent| parent.id == occurrence.activation)
            .ok_or("foreign Generic activation is missing")?;
        let result = parent.result.ok_or("foreign Generic is unfinished")?;
        let (record, _) = self.record(result)?;
        require(
            record.identity == Some(occurrence),
            "foreign Generic indexed another source",
        )?;
        if let Some(CallableOwner::Function(definition)) = record.context.owner {
            charge(self.work, 1)?;
            let owner = self
                .facts
                .functions
                .get(definition.0 as usize)
                .filter(|owner| owner.definition == definition)
                .ok_or("foreign Generic owner has no canonical function slot")?;
            map_work(self.work, self.owners.len())?;
            self.owners.insert(definition, owner.hir_id);
        }
        let rows = self
            .facts
            .evaluations
            .get(parent.start_expression..result.0 as usize)
            .ok_or("foreign Generic has an invalid evaluation interval")?;
        charge(self.work, rows.len())?;
        for record in rows {
            let Some(identity) = record.identity else {
                continue;
            };
            charge(self.work, 1)?;
            let child = self
                .facts
                .activations
                .get(identity.activation.0 as usize)
                .filter(|child| child.id == identity.activation)
                .ok_or("foreign Generic child activation is missing")?;
            if child.parent != Some(parent.id) || child.kind != ActivationKind::Expression {
                continue;
            }
            map_work(self.work, self.children.len())?;
            match self.children.entry((parent.id, identity.source)) {
                Entry::Vacant(entry) => {
                    entry.insert(Child::One(record.id));
                }
                Entry::Occupied(mut entry) => {
                    entry.insert(Child::Duplicate);
                }
            }
        }
        Ok(())
    }

    fn record(
        &mut self,
        id: EvaluationOccurrenceId,
    ) -> Check<(&'a EvaluationRecord, &'a EvaluationActivation)> {
        charge(self.work, 3)?;
        let record = self
            .facts
            .evaluations
            .get(id.0 as usize)
            .filter(|record| record.id == id)
            .ok_or("foreign observation is outside its original arena")?;
        let identity = record
            .identity
            .ok_or("foreign observation has no source identity")?;
        let activation = self
            .facts
            .activations
            .get(identity.activation.0 as usize)
            .filter(|activation| activation.id == identity.activation)
            .ok_or("foreign observation has no actual activation")?;
        let fact = self
            .facts
            .expressions
            .get(id.0 as usize)
            .ok_or("foreign observation has no original value")?;
        require(
            activation.source == Some(identity.source)
                && activation.result == Some(id)
                && activation.scope == record.scope
                && activation.context == record.context
                && fact.source_id == Some(identity.source)
                && fact.allocation_epoch == record.allocation_epoch
                && record.allocation_epoch <= self.facts.allocation_history.len(),
            "foreign observation changed its physical source, context or epoch",
        )?;
        let end = activation
            .end_expression
            .ok_or("foreign activation did not complete")?;
        require(
            activation.start_expression <= id.0 as usize
                && (id.0 as usize) < end
                && end <= self.facts.evaluations.len(),
            "foreign observation escaped its actual evaluation interval",
        )?;
        Ok((record, activation))
    }

    fn physical_application(
        &mut self,
        application: &ExternalApplication,
        instance: &ExternalInstance,
    ) -> Check<(&'a FunctionInfo, EvaluationOccurrenceId)> {
        charge(self.work, 2)?;
        let parent = self
            .facts
            .activations
            .get(application.occurrence.activation.0 as usize)
            .filter(|parent| parent.id == application.occurrence.activation)
            .ok_or("foreign Generic activation is absent")?;
        require(
            parent.kind == ActivationKind::Expression
                && parent.source == Some(application.occurrence.source),
            "foreign specialization borrowed another execution role",
        )?;
        let result = parent
            .result
            .ok_or("foreign Generic has no completed value")?;
        let (record, _) = self.record(result)?;
        require(
            record.identity == Some(application.occurrence),
            "foreign Generic receipt belongs to another actual occurrence",
        )?;
        let node = self
            .hir
            .expression(application.occurrence.source)
            .ok_or("foreign Generic source is absent")?;
        let h::ExprKind::Generic { base, .. } = &node.kind else {
            return Err("foreign specialization source is not an actual Generic".into());
        };
        charge(self.work, 1)?;
        let owner_matches = match (node.info.owner, record.context.owner) {
            (h::LexicalOwner::Module, Some(CallableOwner::Global)) => true,
            (
                h::LexicalOwner::Declaration(statement),
                Some(CallableOwner::Function(definition)),
            ) => {
                map_work(self.work, self.owners.len())?;
                self.owners.get(&definition) == Some(&Some(statement))
            }
            (h::LexicalOwner::Lambda(source), Some(CallableOwner::Lambda(site))) => self
                .facts
                .closure_sites
                .get(site.0 as usize)
                .is_some_and(|actual| actual.id == site && actual.source == source),
            _ => false,
        };
        require(
            owner_matches,
            "foreign Generic changed its original lexical owner",
        )?;
        map_work(self.work, self.children.len())?;
        require(
            matches!(self.children.get(&(parent.id, *base)), Some(Child::One(id)) if *id == application.base),
            "foreign specialization lost its unique direct base observation",
        )?;
        let (base_record, child) = self.record(application.base)?;
        require(
            child.kind == ActivationKind::Expression
                && child.parent == Some(parent.id)
                && child.source == Some(*base)
                && base_record.context == record.context
                && base_record.scope == record.scope
                && child.context == parent.context
                && child.scope == parent.scope
                && base_record.allocation_epoch <= record.allocation_epoch
                && application.base.0 < result.0,
            "foreign specialization borrowed a sibling base or caller frame",
        )?;
        charge(self.work, 2)?;
        let [Callable::Named(template)] = self.facts.expressions[application.base.0 as usize]
            .value
            .callables
            .as_slice()
        else {
            return Err("foreign specialization base is not one actual named template".into());
        };
        let template = self
            .facts
            .functions
            .get(*template)
            .ok_or("foreign template callable is outside its arena")?;
        require(
            template.definition == instance.template
                && template.hir_id == Some(instance.declaration)
                && template.syntax.body.is_none()
                && !template.syntax.generics.is_empty(),
            "foreign specialization base names another original declaration",
        )?;
        require(
            matches!(self.facts.expressions[result.0 as usize].value.callables.as_slice(), [Callable::Named(callable)] if *callable == instance.callable),
            "foreign Generic result changed its actual selected callable",
        )?;
        super::clone_work::ty(self.work, &instance.callable_type, 0)
            .ok_or("foreign callable cache exceeds its type work bound")?;
        super::clone_work::ty(
            self.work,
            &self.facts.expressions[result.0 as usize].value.ty,
            0,
        )
        .ok_or("foreign actual callable exceeds its type work bound")?;
        require(
            self.facts.expressions[result.0 as usize].value.ty == instance.callable_type,
            "foreign instance and its actual Generic disagree about the callable cache",
        )?;
        map_work(self.work, self.covered.len())?;
        require(
            self.covered.insert(application.occurrence),
            "one foreign Generic occurrence has multiple specialization receipts",
        )?;
        Ok((template, result))
    }

    fn generated_tree(&mut self, instance: &ExternalInstance) -> Check {
        charge(self.work, 2)?;
        let first = instance
            .applications
            .first()
            .ok_or("foreign generated declaration has no creation occurrence")?;
        let node = self
            .hir
            .statement(instance.generated)
            .ok_or("foreign generated declaration is absent")?;
        let h::NodeOrigin::Generated {
            generation,
            anchor,
            kind: h::GeneratedKind::StaticSpecialization,
        } = node.info.origin
        else {
            return Err("foreign instance is not a canonical static specialization".into());
        };
        require(
            anchor == h::NodeId::Expr(first.occurrence.source)
                && node.info.owner == h::LexicalOwner::Module
                && self.hir.generated_roots().get(generation as usize)
                    == Some(&h::NodeId::Stmt(instance.generated)),
            "foreign generated declaration changed its creation anchor or generation",
        )?;
        charge(self.work, 1)?;
        let mut pending = vec![h::NodeId::Stmt(instance.generated)];
        let mut seen = BTreeSet::new();
        while let Some(id) = pending.pop() {
            map_work(self.work, seen.len())?;
            if !seen.insert(id) {
                continue;
            }
            charge(self.work, 1)?;
            require(
                self.hir
                    .info(id)
                    .is_some_and(|info| info.origin == node.info.origin),
                "foreign generated subtree borrowed another generation",
            )?;
            let children = self
                .hir
                .children_with_work(id, self.work)
                .map_err(|error| error.to_string())?;
            charge(self.work, children.len())?;
            pending.extend(children);
        }
        Ok(())
    }

    fn application_recipe(
        &mut self,
        instance: &ExternalInstance,
        index: usize,
        application: &ExternalApplication,
        info: &FunctionInfo,
        sites: &super::record_bound_validation::SourceSites<'_>,
    ) -> Check {
        let (template, _) = self.physical_application(application, instance)?;
        require(
            !template.typing_environment.is_poisoned()
                && !info.typing_environment.is_poisoned()
                && info.typing_environment.id() == template.typing_environment.id(),
            "foreign instance replaced its original declaration environment",
        )?;
        charge(
            self.work,
            instance.declaration_name.len().div_ceil(32) + template.syntax.name.len().div_ceil(32),
        )?;
        require(
            instance.declaration_name == template.syntax.name,
            "foreign instance changed its original declaration name",
        )?;
        map_work(self.work, sites.expressions.len())?;
        let syntax = sites
            .expressions
            .get(&application.occurrence.source)
            .ok_or("foreign creation has no authenticated original source syntax")?;
        let ExprKind::Generic { base, arguments } = &syntax.kind else {
            return Err("foreign creation source is not an original GenericApply".into());
        };
        let h::ExprKind::Generic {
            base: original_base,
            arguments: original_arguments,
        } = &self
            .hir
            .expression(application.occurrence.source)
            .ok_or("foreign creation HIR is absent")?
            .kind
        else {
            return Err("foreign creation HIR is not a Generic".into());
        };
        charge(self.work, arguments.len())?;
        require(
            syntax.hir_id == Some(application.occurrence.source)
                && base.hir_id == Some(*original_base)
                && original_arguments.len() == arguments.len()
                && original_arguments
                    .iter()
                    .zip(arguments)
                    .all(|(id, syntax)| syntax.hir_id == Some(*id)),
            "foreign creation changed its actual static argument coordinates",
        )?;
        let expected = super::external_instances::instantiate(
            template,
            arguments,
            &self.facts.external_type_declarations,
            self.hir,
            self.facts
                .target_layout
                .ok_or("foreign instance has no selected target layout")?,
            index,
            self.work,
        )
        .map_err(failure)?;
        self.syntax(&expected.syntax, instance.generated, false)?;
        charge(self.work, expected.arguments.len())?;
        require(
            expected.arguments.len() == instance.arguments.len()
                && expected.arguments.len() == template.syntax.generics.len(),
            "foreign static argument cache changed its arity",
        )?;
        for ((expected, (name, stored)), parameter) in expected
            .arguments
            .iter()
            .zip(&instance.arguments)
            .zip(&template.syntax.generics)
        {
            charge(
                self.work,
                name.len().div_ceil(32) + parameter.name.len().div_ceil(32),
            )?;
            require(
                *name == parameter.name && normalized_equal(expected, stored, self.work)?,
                "foreign static argument cache differs from the actual template application",
            )?;
        }
        Ok(())
    }

    fn syntax(
        &mut self,
        syntax: &ast::Function,
        generated: ril_compiler_core::ids::StmtId,
        identified: bool,
    ) -> Check {
        admit(syntax, self.work)?;
        admit(syntax, self.work)?;
        let mut statement = ast::Stmt {
            hir_id: Some(generated),
            span: syntax.span,
            kind: ast::StmtKind::Function(syntax.clone()),
        };
        let result = if identified {
            self.hir
                .validate_statement_syntax(&mut statement, generated, h::HirLimits::default())
        } else {
            self.hir.validate_catalog_declaration(
                &mut statement,
                generated,
                h::HirLimits::default(),
            )
        };
        result.map_err(|error| {
            format!("foreign generated signature differs from its recipe: {error}")
        })
    }
}

/// A query-local authenticated recipe. It is never retained as another fact
/// table and cannot be reused against a different mutable facts snapshot.
pub(crate) struct AuthenticatedExternalInstance<'a> {
    function: &'a FunctionInfo,
}

impl AuthenticatedExternalInstance<'_> {
    pub(crate) fn function(&self) -> &FunctionInfo {
        self.function
    }
}

pub(crate) fn application_instance<'a>(
    facts: &'a SemanticFacts,
    observation: EvaluationOccurrenceId,
    sites: &super::record_bound_validation::SourceSites<'_>,
    work: &mut usize,
) -> Check<Option<AuthenticatedExternalInstance<'a>>> {
    charge(work, 3)?;
    let fact = facts
        .expressions
        .get(observation.0 as usize)
        .ok_or("foreign callee observation is absent")?;
    let [Callable::Named(callable)] = fact.value.callables.as_slice() else {
        return Ok(None);
    };
    let info = facts
        .functions
        .get(*callable)
        .ok_or("foreign callee is outside its function arena")?;
    charge(work, facts.external_instances.len())?;
    let mut candidates = facts
        .external_instances
        .iter()
        .enumerate()
        .filter(|(_, instance)| instance.callable == *callable);
    let Some((index, instance)) = candidates.next() else {
        let generated = info
            .hir_id
            .and_then(|id| facts.semantic_hir.as_deref()?.statement(id))
            .is_some_and(|node| {
                matches!(
                    node.info.origin,
                    h::NodeOrigin::Generated {
                        kind: h::GeneratedKind::StaticSpecialization,
                        ..
                    }
                )
            });
        require(
            !generated,
            "generated foreign callee lost its instance recipe",
        )?;
        return Ok(None);
    };
    require(
        candidates.next().is_none(),
        "foreign callee has multiple instance recipes",
    )?;
    let hir = facts
        .semantic_hir
        .as_deref()
        .ok_or("foreign callee has no semantic HIR")?;
    charge(work, 1 + instance.applications.len())?;
    let record = facts
        .evaluations
        .get(observation.0 as usize)
        .filter(|record| record.id == observation)
        .ok_or("foreign callee has no original evaluation record")?;
    let occurrence = record
        .identity
        .ok_or("foreign callee has no original occurrence")?;
    let mut applications = instance
        .applications
        .iter()
        .filter(|application| application.occurrence == occurrence);
    let application = applications
        .next()
        .ok_or("foreign callee lost this actual Generic receipt")?;
    require(
        applications.next().is_none(),
        "foreign callee repeats an actual Generic receipt",
    )?;
    let first = instance
        .applications
        .first()
        .ok_or("foreign callee has no original creation")?;
    let mut replay = Replay {
        facts,
        hir,
        work,
        children: BTreeMap::new(),
        instances: BTreeMap::new(),
        owners: BTreeMap::new(),
        covered: BTreeSet::new(),
    };
    replay.generated_tree(instance)?;
    require(
        info.hir_id == Some(instance.generated) && info.definition != instance.template,
        "foreign callee did not retain its distinct generated declaration",
    )?;
    replay.syntax(&instance.syntax, instance.generated, true)?;
    replay.syntax(&info.syntax, instance.generated, true)?;
    replay.index_application(first.occurrence)?;
    replay.application_recipe(instance, index, first, info, sites)?;
    if first.occurrence != application.occurrence {
        replay.index_application(application.occurrence)?;
        replay.application_recipe(instance, index, application, info, sites)?;
    }
    Ok(Some(AuthenticatedExternalInstance { function: info }))
}

pub(crate) fn validate(facts: &SemanticFacts, work: &mut usize) -> Check {
    charge(work, 1)?;
    let Some(hir) = facts.semantic_hir.as_deref() else {
        return require(
            facts.external_instances.is_empty(),
            "foreign instance has no original HIR",
        );
    };
    let mut replay = Replay {
        facts,
        hir,
        work,
        children: BTreeMap::new(),
        instances: BTreeMap::new(),
        owners: BTreeMap::new(),
        covered: BTreeSet::new(),
    };
    charge(
        replay.work,
        facts.evaluations.len() + facts.external_instances.len() + facts.functions.len(),
    )?;
    for function in &facts.functions {
        map_work(replay.work, replay.owners.len())?;
        match replay.owners.entry(function.definition) {
            Entry::Vacant(entry) => {
                entry.insert(function.hir_id);
            }
            Entry::Occupied(mut entry) => {
                if *entry.get() != function.hir_id {
                    entry.insert(None);
                }
            }
        }
    }
    for record in &facts.evaluations {
        let Some(identity) = record.identity else {
            continue;
        };
        charge(replay.work, 1)?;
        let activation = facts
            .activations
            .get(identity.activation.0 as usize)
            .filter(|activation| activation.id == identity.activation)
            .ok_or("foreign input indexing found a missing activation")?;
        if activation.kind != ActivationKind::Expression {
            continue;
        }
        if let Some(parent) = activation.parent {
            map_work(replay.work, replay.children.len())?;
            match replay.children.entry((parent, identity.source)) {
                Entry::Vacant(entry) => {
                    entry.insert(Child::One(record.id));
                }
                Entry::Occupied(mut entry) => {
                    entry.insert(Child::Duplicate);
                }
            }
        }
    }
    let sites = super::record_bound_validation::source_sites_base_with_work(facts, replay.work)?;
    let mut generated = BTreeSet::new();
    for (index, instance) in facts.external_instances.iter().enumerate() {
        map_work(replay.work, replay.instances.len())?;
        require(
            replay.instances.insert(instance.callable, index).is_none(),
            "foreign instances repeat a selected callable",
        )?;
        map_work(replay.work, generated.len())?;
        require(
            generated.insert(instance.generated),
            "foreign instances repeat a generated declaration",
        )?;
        replay.generated_tree(instance)?;
        charge(replay.work, 1 + instance.applications.len())?;
        let info = facts
            .functions
            .get(instance.callable)
            .ok_or("foreign instance callable is missing")?;
        require(
            info.hir_id == Some(instance.generated) && info.definition != instance.template,
            "foreign instance did not retain its distinct generated function",
        )?;
        replay.syntax(&instance.syntax, instance.generated, true)?;
        replay.syntax(&info.syntax, instance.generated, true)?;
        for application in &instance.applications {
            replay.application_recipe(instance, index, application, info, &sites)?;
        }
    }
    charge(replay.work, hir.generated_roots().len())?;
    for root in hir.generated_roots() {
        if hir.info(*root).is_some_and(|info| {
            matches!(
                info.origin,
                h::NodeOrigin::Generated {
                    kind: h::GeneratedKind::StaticSpecialization,
                    ..
                }
            )
        }) {
            let h::NodeId::Stmt(id) = root else {
                return Err("foreign specialization has no generated declaration root".into());
            };
            map_work(replay.work, generated.len())?;
            require(
                generated.contains(id),
                "generated foreign declaration lost its instance recipe",
            )?;
        }
    }
    charge(replay.work, facts.evaluations.len())?;
    for record in &facts.evaluations {
        let Some(identity) = record.identity else {
            continue;
        };
        let Some(h::Expr {
            kind: h::ExprKind::Generic { base, .. },
            ..
        }) = hir.expression(identity.source)
        else {
            continue;
        };
        let (_, activation) = replay.record(record.id)?;
        if activation.kind != ActivationKind::Expression {
            continue;
        }
        map_work(replay.work, replay.children.len())?;
        let Some(Child::One(base_observation)) =
            replay.children.get(&(identity.activation, *base)).copied()
        else {
            return Err("actual Generic lost its unique direct base evaluation".into());
        };
        charge(replay.work, 2)?;
        let [Callable::Named(template)] = facts
            .expressions
            .get(base_observation.0 as usize)
            .ok_or("foreign Generic base value is missing")?
            .value
            .callables
            .as_slice()
        else {
            continue;
        };
        let template = facts
            .functions
            .get(*template)
            .ok_or("foreign Generic base callable is missing")?;
        let external_template = template.hir_id.and_then(|id| hir.statement(id)).is_some_and(|node| {
            matches!(&node.kind, h::StmtKind::Function(function) if function.body.is_none() && !function.generics.is_empty())
        });
        let callables = &facts.expressions[record.id.0 as usize].value.callables;
        charge(replay.work, callables.len())?;
        let mut actual_external = false;
        for callable in callables {
            if let Callable::Named(id) = callable {
                map_work(replay.work, replay.instances.len())?;
                actual_external |= replay.instances.contains_key(id);
            }
        }
        if external_template || actual_external {
            map_work(replay.work, replay.covered.len())?;
            require(
                replay.covered.contains(&identity),
                "actual foreign Generic lost its independent specialization recipe",
            )?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckOptions, Session, session::ProjectSource};

    fn checked() -> SemanticFacts {
        let case =
            ril_test::case_by_id("tests/conformance/numeric.ril::external-const-floating-defaults");
        let directory = std::path::Path::new("external-instance-review");
        let program = Session::with_project(
            directory.join(&case.root),
            case.files
                .iter()
                .map(|file| ProjectSource {
                    path: directory.join(&file.name),
                    bytes: file.bytes.clone(),
                })
                .collect(),
            CheckOptions::default(),
        )
        .unwrap()
        .verify()
        .unwrap();
        let facts = program.facts().clone();
        assert!(!facts.external_instances.is_empty());
        assert_eq!(validate(&facts, &mut 4_000_000), Ok(()));
        facts
    }

    #[test]
    fn foreign_instances_require_original_arguments_physical_bases_and_generated_headers() {
        let baseline = checked();
        assert!(baseline.external_instances.len() >= 2);
        for mutation in 0..9 {
            let mut changed = baseline.clone();
            match mutation {
                0 => changed.external_instances.clear(),
                1 => changed.external_instances[0].applications.clear(),
                2 => {
                    changed.external_instances[0].applications[0].base =
                        baseline.external_instances[1].applications[0].base
                }
                3 => {
                    changed.external_instances[0].applications[0].occurrence =
                        baseline.external_instances[1].applications[0].occurrence
                }
                4 => {
                    changed.external_instances[0].generated =
                        baseline.external_instances[1].generated
                }
                5 => {
                    let callable = changed.external_instances[0].callable;
                    changed.functions[callable].typing_environment =
                        super::super::context::FrozenEnvironment::default();
                }
                6 => {
                    assert!(
                        changed.external_instances[0].syntax.parameters[0]
                            .default
                            .is_some()
                    );
                    changed.external_instances[0].syntax.parameters[0].default = None;
                }
                7 => {
                    assert_ne!(
                        static_eval::normalized_argument_key(
                            &baseline.external_instances[0].arguments[0].1
                        ),
                        static_eval::normalized_argument_key(
                            &baseline.external_instances[1].arguments[0].1
                        ),
                    );
                    changed.external_instances[0].arguments =
                        baseline.external_instances[1].arguments.clone();
                }
                8 => {
                    changed.external_instances[0].declaration =
                        baseline.external_instances[0].generated
                }
                _ => unreachable!(),
            }
            assert!(
                validate(&changed, &mut 4_000_000).is_err(),
                "foreign mutation {mutation} was accepted"
            );
        }
        assert!(validate(&baseline, &mut 0).is_err());
    }

    #[test]
    fn a_foreign_callee_source_query_authenticates_its_recipe_without_global_validation() {
        let baseline = checked();
        let instance = &baseline.external_instances[0];
        let application = &instance.applications[0];
        let observation = baseline.activations[application.occurrence.activation.0 as usize]
            .result
            .unwrap();
        let sites = super::super::record_bound_validation::source_sites_base_with_work(
            &baseline,
            &mut 4_000_000,
        )
        .unwrap();
        let authenticated = application_instance(&baseline, observation, &sites, &mut 4_000_000)
            .unwrap()
            .unwrap();
        assert_eq!(authenticated.function().hir_id, Some(instance.generated));
        for mutation in 0..3 {
            let mut changed = baseline.clone();
            match mutation {
                0 => changed.external_instances.clear(),
                1 => changed.external_instances[0].applications.clear(),
                2 => {
                    changed.external_instances[0].applications[0].base =
                        baseline.external_instances[1].applications[0].base
                }
                _ => unreachable!(),
            }
            let sites = super::super::record_bound_validation::source_sites_base_with_work(
                &changed,
                &mut 4_000_000,
            )
            .unwrap();
            assert!(
                application_instance(&changed, observation, &sites, &mut 4_000_000).is_err(),
                "standalone foreign Source mutation {mutation} was accepted"
            );
        }
    }

    #[test]
    fn foreign_default_sources_require_authenticated_generated_declarations() {
        use super::super::{
            record_bound_validation::OriginalOperandSources,
            source_types::{SourceScalar, WorkLimit},
        };
        let baseline = checked();
        let instance = &baseline.external_instances[0];
        let default = instance.syntax.parameters[0].default.as_ref().unwrap();
        let source = default.hir_id.unwrap();
        let record = baseline
            .evaluations
            .iter()
            .find(|record| {
                record
                    .identity
                    .is_some_and(|identity| identity.source == source)
                    && record.context.default_use.is_some()
            })
            .expect("the generated default has an actual default-use observation");
        let observation = record.id.0 as usize;
        let mut work = 16_000_000;
        let originals = OriginalOperandSources::new_with_work(&baseline, &mut work).unwrap();
        let (schema, _) = originals
            .observed_with_work(source, observation, &mut work)
            .unwrap();
        let (schema, _) =
            schema.expect("the foreign default retains its complete original scalar Source");
        assert!(matches!(
            schema.scalar_representation(&mut WorkLimit::new(work)),
            Ok(Some(SourceScalar::F32 | SourceScalar::F64))
        ));

        for mutation in 0..5 {
            let mut changed = baseline.clone();
            match mutation {
                0 => changed.external_instances.clear(),
                1 => {
                    changed.external_instances[0].generated =
                        baseline.external_instances[1].generated
                }
                2 => {
                    changed.external_instances[0].applications[0].base =
                        baseline.external_instances[1].applications[0].base
                }
                3 => changed.external_instances[0].syntax.parameters[0].default = None,
                4 => {
                    changed.external_instances[0].syntax.parameters[0]
                        .default
                        .as_mut()
                        .unwrap()
                        .hir_id = baseline.external_instances[1].syntax.parameters[0]
                        .default
                        .as_ref()
                        .unwrap()
                        .hir_id
                }
                _ => unreachable!(),
            }
            let mut work = 16_000_000;
            let result = OriginalOperandSources::new_with_work(&changed, &mut work)
                .and_then(|originals| originals.observed_with_work(source, observation, &mut work));
            assert!(
                result.is_err(),
                "foreign default Source mutation {mutation} was accepted"
            );
        }
    }
}
