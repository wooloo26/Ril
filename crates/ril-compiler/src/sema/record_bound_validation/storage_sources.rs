//! Replay immutable storage declarations and every actual assignment occurrence.
//! Source rows are duties, never a substitute for the ordinary access checker.
use super::*;
use crate::sema::{
    effect_identity::InvocationContext,
    facts::ScopeId,
    model::{BindingId, Callable, Constant, HandlerFact},
    source_reception::{self, Construction},
    source_types::projection_receipts::{
        self, ProjectionOccurrence, ProjectionReceipts, SourceRead,
    },
    storage_sources::{BindingSource, StorageDestination, StorageObservation},
};

type PatternPlan = BTreeMap<
    ril_compiler_core::ids::PatternId,
    BTreeMap<String, Option<Vec<ril_compiler_core::projection::TypeProjection>>>,
>;
type SourceRoots = BTreeMap<
    (
        ril_compiler_core::ids::PatternId,
        usize,
        crate::sema::context::FrozenEnvId,
    ),
    Option<crate::sema::source_types::SourceSchema>,
>;

fn origin_work(work: &mut usize, units: usize) -> Check {
    *work = work
        .checked_sub(units)
        .ok_or("binding origin replay work exhausted")?;
    Ok(())
}

type DeclarationInputs = BTreeMap<ril_compiler_core::ids::ExprId, ril_compiler_core::ids::StmtId>;

#[derive(Clone, Copy, PartialEq, Eq)]
enum StorageBirthRole {
    Expression,
    Declaration,
    ProtectedAnswer,
}

/// Unknown tags retain the success-path reception obligation. Only a known
/// incompatible tag can rule that path out; no name census or producer ID can
/// erase the obligation of an actually evaluated guarded initializer.
fn initializer_may_bind(
    hir: &crate::hir::nodes::HirProgram,
    pattern: ril_compiler_core::ids::PatternId,
    value: &Value,
    work: &mut usize,
    depth: usize,
) -> Check<bool> {
    use crate::hir::nodes::PatternKind;
    *work = work
        .checked_sub(1)
        .ok_or("guarded reception tag work exhausted")?;
    require(depth < 128, "guarded reception pattern depth exceeded")?;
    let original = hir
        .pattern(pattern)
        .ok_or("guarded reception lost its original pattern")?;
    Ok(match &original.kind {
        PatternKind::Constructor { path, .. } => {
            *work = work
                .checked_sub(path.len())
                .ok_or("guarded constructor work exhausted")?;
            for name in path {
                *work = work
                    .checked_sub(name.len().div_ceil(32))
                    .ok_or("guarded constructor text work exhausted")?;
            }
            let standard = match path.as_slice() {
                [name] => Some(name.strip_prefix("Prelude::").unwrap_or(name)),
                [module, name] if module == "Prelude" => Some(name.as_str()),
                _ => None,
            };
            match standard {
                Some("Some") => value.option_tag != Some(false),
                Some("None") => value.option_tag != Some(true),
                Some("Ok") => value.result_tag != Some(false),
                Some("Err") => value.result_tag != Some(true),
                _ => value
                    .variant_tag
                    .as_ref()
                    .is_none_or(|tag| tag == &path.join("::")),
            }
        }
        PatternKind::Literal(Literal::Bool(expected)) => value
            .constant
            .as_ref()
            .is_none_or(|actual| actual != &Constant::Bool(!expected)),
        PatternKind::Mode { pattern, .. } => {
            initializer_may_bind(hir, *pattern, value, work, depth + 1)?
        }
        PatternKind::Alternative(alternatives) => {
            let mut possible = false;
            for alternative in alternatives {
                possible |= initializer_may_bind(hir, *alternative, value, work, depth + 1)?;
            }
            possible
        }
        _ => true,
    })
}

impl Replay<'_> {
    fn storage_declaration_inputs(&self, work: &mut usize) -> Check<DeclarationInputs> {
        use crate::hir::nodes::{ExprKind as HirExpr, LexicalOwner, StmtKind as HirStmt};
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("declaration inputs have no HIR")?;
        origin_work(work, hir.roots().len() + hir.declaration_roots().len())?;
        let roots: BTreeSet<_> = hir.roots().iter().copied().collect();
        let mut inputs = BTreeMap::new();
        for root in hir.declaration_roots() {
            require(
                roots.contains(root),
                "declaration input is not an original unit root",
            )?;
            let statement = hir
                .statement(*root)
                .ok_or("declaration input root is absent")?;
            if let HirStmt::Binding {
                is_meta: false,
                mode: ril_syntax::ast::BindingMode::Let,
                ty: Some(_),
                value,
                fallback: None,
                ..
            } = &statement.kind
                && matches!(
                    hir.expression(*value).map(|value| &value.kind),
                    Some(HirExpr::Ambient)
                )
            {
                require(
                    statement.info.owner == LexicalOwner::Module,
                    "declaration data belongs to another lexical owner",
                )?;
                origin_work(work, 1)?;
                require(
                    inputs.insert(*value, *root).is_none(),
                    "declaration inputs share one ambient source",
                )?;
            }
        }
        Ok(inputs)
    }

    /// Interpret physical observations through their actual source role.
    /// In particular, a Resume request is not its later continuation answer,
    /// and an arbitrary emission is never an executable initializer.
    fn storage_birth_role(
        &self,
        activation: &crate::sema::application_effect::EvaluationActivation,
        declarations: &DeclarationInputs,
        work: &mut usize,
    ) -> Check<Option<StorageBirthRole>> {
        use crate::hir::nodes::ExprKind as HirExpr;
        use crate::sema::application_effect::ActivationKind;
        origin_work(work, 1)?;
        let source = activation
            .source
            .ok_or("binding birth has no original source")?;
        let result = activation
            .result
            .ok_or("binding birth has no physical result")?;
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("binding birth has no HIR")?;
        let syntax = hir
            .expression(source)
            .ok_or("binding birth source is outside HIR")?;
        let record = self
            .facts
            .evaluations
            .get(result.0 as usize)
            .ok_or("binding birth result is absent")?;
        let fact = self
            .facts
            .expressions
            .get(result.0 as usize)
            .ok_or("binding birth value is absent")?;
        require(
            self.facts
                .activations
                .get(activation.id.0 as usize)
                .is_some_and(|actual| actual.id == activation.id)
                && record.id == result
                && record.identity
                    == Some(crate::sema::application_effect::OccurrenceIdentity {
                        source,
                        activation: activation.id,
                    })
                && record.scope == activation.scope
                && record.context == activation.context
                && record.allocation_epoch == fact.allocation_epoch
                && fact.source_id == Some(source),
            "binding birth borrowed another physical result",
        )?;
        let resume = matches!(
            syntax.kind,
            HirExpr::Control {
                operation: ril_syntax::ast::ControlOperation::Resume,
                ..
            }
        );
        match activation.kind {
            ActivationKind::Expression => {
                require(
                    !resume && !matches!(syntax.kind, HirExpr::Ambient),
                    "declaration data or a Resume request borrowed an ordinary expression role",
                )?;
                Ok(Some(StorageBirthRole::Expression))
            }
            ActivationKind::ControlTransfer => {
                require(
                    resume,
                    "control-transfer birth is not an original Resume request",
                )?;
                Ok(None)
            }
            ActivationKind::Emission if matches!(syntax.kind, HirExpr::Ambient) => {
                require(
                    declarations.contains_key(&source),
                    "ambient declaration lost its canonical input authorization",
                )?;
                require(
                    activation.scope == ScopeId(0)
                        && activation.context.owner == Some(CallableOwner::Global)
                        && activation.context.invocation.is_none()
                        && activation.context.closure.is_none()
                        && activation.context.closure_invocation.is_none()
                        && activation.context.default_use.is_none()
                        && !activation.context.budget_validation
                        && fact.value.permission == crate::sema::facts::Permission::Read
                        && fact.value.publication == Publication::Immutable
                        && !fact.value.construction,
                    "declaration data lost its immutable module reception",
                )?;
                Ok(Some(StorageBirthRole::Declaration))
            }
            ActivationKind::Emission if resume => {
                origin_work(work, self.facts.resumption_steps.len())?;
                let mut steps = self
                    .facts
                    .resumption_steps
                    .iter()
                    .filter(|step| step.continuation_expression == result.0 as usize);
                let Some(step) = steps.next() else {
                    return Ok(None);
                };
                require(
                    steps.next().is_none()
                        && step.id.0 == result.0
                        && step.resume_source == source
                        && step.owner == activation.scope
                        && step.context == activation.context
                        && step.continuation_epoch == fact.allocation_epoch
                        && step.continuation == fact.value.cause
                        && step.continuation_value.value.cause == fact.value.cause,
                    "protected answer birth lost its unique actual resumption step",
                )?;
                Ok(Some(StorageBirthRole::ProtectedAnswer))
            }
            ActivationKind::Emission => Ok(None),
        }
    }

    fn storage_resource_lease_origin(
        &self,
        id: BindingId,
        pattern: ril_compiler_core::ids::PatternId,
        work: &mut usize,
    ) -> Check<bool> {
        use crate::hir::nodes::{GeneratedKind, NodeId, NodeOrigin, PatternKind};
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("resource receiver has no HIR")?;
        let original = hir
            .pattern(pattern)
            .ok_or("binding pattern is outside its original HIR")?;
        let NodeOrigin::Generated {
            generation,
            anchor: NodeId::Expr(source),
            kind: GeneratedKind::ResourceLease,
        } = original.info.origin
        else {
            return Ok(false);
        };
        let binding = self
            .facts
            .bindings
            .get(id)
            .ok_or("resource receiver binding is absent")?;
        require(
            hir.generated_roots().get(generation as usize) == Some(&NodeId::Pattern(pattern))
                && hir
                    .expression(source)
                    .is_some_and(|anchor| anchor.info.owner == original.info.owner)
                && matches!(&original.kind, PatternKind::Name(name) if name == &binding.name),
            "resource receiver lost its canonical generated root",
        )?;
        let mut parents = BTreeSet::new();
        origin_work(
            work,
            self.facts.copy_invocations.len() + self.facts.closure_invocations.len(),
        )?;
        for call in &self.facts.copy_invocations {
            if call.caller_activation == Some(binding.owner)
                && call.entry.caller_context == binding.context
                && call.entry.arguments.first().is_some_and(|(mode, input)| {
                    *mode == crate::sema::model::Mode::Write
                        && input.value.sources == BTreeSet::from([id])
                        && input.value.temporary
                        && input.value.scoped.contains(&id)
                })
                && let Some(parent) = call.entry.parent
            {
                parents.insert(parent);
            }
        }
        for call in &self.facts.closure_invocations {
            if call.caller_activation == binding.owner
                && call.entry.caller_context == binding.context
                && call
                    .entry
                    .arguments
                    .first()
                    .is_some_and(|(mode, input, _)| {
                        *mode == ril_syntax::ast::ParameterMode::Mut
                            && input.sources == BTreeSet::from([id])
                            && input.temporary
                            && input.scoped.contains(&id)
                    })
                && let Some(parent) = call.entry.parent
            {
                parents.insert(parent);
            }
        }
        require(
            parents.len() == 1,
            "resource receiver lost its unique actual callback origin",
        )?;
        let parent = self
            .facts
            .activations
            .get(parents.first().unwrap().0 as usize)
            .ok_or("resource receiver call activation is absent")?;
        require(
            parent.source == Some(source)
                && binding.birth
                    == Some(crate::sema::application_effect::OccurrenceIdentity {
                        source,
                        activation: parent.id,
                    })
                && parent.kind == crate::sema::application_effect::ActivationKind::Expression
                && self.facts.scopes.parent(&binding.owner) == Some(&parent.scope),
            "resource receiver borrowed another builtin call or helper frame",
        )?;
        let mut builtin = None;
        origin_work(work, self.facts.copy_call_events.len())?;
        for event in &self.facts.copy_call_events {
            if event.source_id != Some(source) {
                continue;
            }
            let Some(index) = event.callee_expression else {
                continue;
            };
            let Some(record) = self.facts.evaluations.get(index) else {
                continue;
            };
            let Some(entered) = record
                .identity
                .and_then(|identity| self.facts.activations.get(identity.activation.0 as usize))
            else {
                continue;
            };
            if entered.parent != Some(parent.id) || record.context != parent.context {
                continue;
            }
            let Some(callee) = self.facts.expressions.get(index) else {
                continue;
            };
            let [Callable::Builtin(name)] = callee.value.callables.as_slice() else {
                continue;
            };
            require(
                builtin.replace(name.as_str()).is_none(),
                "resource receiver has ambiguous physical builtin calls",
            )?;
        }
        let (name, mode) = match builtin {
            Some("File::with_file") => (
                "ril__with_file_lease",
                ril_syntax::ast::BindingMode::ScopedMut,
            ),
            Some("Process::with_child") => (
                "ril__with_child_lease",
                ril_syntax::ast::BindingMode::LetMut,
            ),
            _ => return Err("resource receiver is not a compiler-owned builtin lease".into()),
        };
        origin_work(
            work,
            binding.value.origins.nodes.len() + self.facts.cleanup_events.len(),
        )?;
        require(
            binding.name == name
                && binding.mode == mode
                && binding.context.owner.is_none()
                && binding.value.scoped.contains(&id)
                && !binding.value.origins.nodes.is_empty()
                && binding.value.origins.nodes.iter().all(|node| {
                    self.facts
                        .heap
                        .nodes
                        .get(node.0 as usize)
                        .is_some_and(|node| {
                            node.owner == binding.owner
                                && matches!(
                                    node.kind,
                                    crate::sema::facts::OriginKind::Fresh(_)
                                        | crate::sema::facts::OriginKind::Older(_)
                                )
                        })
                })
                && self.facts.cleanup_events.iter().any(|cleanup| {
                    cleanup.binding == id
                        && cleanup.owner == binding.owner
                        && self.facts.explanations.kinds.get(cleanup.cause.0 as usize)
                            == Some(&crate::sema::facts::CauseKind::Cleanup)
                }),
            "resource receiver lost its actual resource or cleanup origin",
        )?;
        Ok(true)
    }

    /// Every actual source-pattern birth has an introducer, independently of
    /// optional Source caches, receiving rows and the initializer's mutable
    /// abstract tags. Missing metadata cannot turn a receiver into a failure.
    fn storage_binding_origins(
        &self,
        sites: &super::explicit_named::SourceSites<'_>,
        introduced: &BTreeMap<
            (CallableOwner, ril_compiler_core::ids::ExprId),
            BTreeMap<ril_compiler_core::ids::PatternId, BTreeSet<String>>,
        >,
        declaration_inputs: &DeclarationInputs,
        work: &mut usize,
    ) -> Check {
        use crate::hir::nodes::ExprKind as HirExpr;
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("binding origins have no HIR")?;
        let mut generated_binders = BTreeMap::<_, Vec<_>>::new();
        origin_work(work, self.facts.bindings.len())?;
        for (id, binding) in self.facts.bindings.iter().enumerate() {
            if let Some(pattern) = binding.pattern {
                origin_work(work, 1)?;
                generated_binders.entry(pattern).or_default().push(id);
            }
        }
        for (ordinal, root) in hir.generated_roots().iter().enumerate() {
            origin_work(work, 1)?;
            let crate::hir::nodes::NodeId::Pattern(pattern) = root else {
                continue;
            };
            let original = hir
                .pattern(*pattern)
                .ok_or("generated receiver root has no pattern")?;
            require(
                matches!(original.info.origin,
                crate::hir::nodes::NodeOrigin::Generated {
                    generation, anchor: crate::hir::nodes::NodeId::Expr(_),
                    kind: crate::hir::nodes::GeneratedKind::ResourceLease,
                } if generation as usize == ordinal),
                "generated receiver root changed its generation or anchor",
            )?;
            let bindings = generated_binders
                .get(pattern)
                .ok_or("generated receiver has no actual binding")?;
            require(
                bindings.len() == 1,
                "generated receiver reused one introducer for multiple births",
            )?;
            self.storage_resource_lease_origin(bindings[0], *pattern, work)?;
        }
        let mut aliases = BTreeMap::<_, BTreeMap<String, BTreeSet<_>>>::new();
        for source in sites.expressions.keys() {
            origin_work(work, 1)?;
            let expression = hir
                .expression(*source)
                .ok_or("alias origin has no HIR expression")?;
            let roots = match &expression.kind {
                HirExpr::Match {
                    arms,
                    type_match: false,
                    ..
                } => {
                    origin_work(work, arms.len())?;
                    arms.iter().map(|arm| arm.pattern).collect::<Vec<_>>()
                }
                HirExpr::For { pattern, .. } => {
                    origin_work(work, 1)?;
                    vec![*pattern]
                }
                _ => continue,
            };
            for root in roots {
                let plan = hir
                    .pattern_bindings(root, work)
                    .map_err(|error| error.to_string())?;
                origin_work(work, plan.len().saturating_mul(3))?;
                for binding in plan {
                    aliases
                        .entry(binding.pattern)
                        .or_default()
                        .entry(binding.name)
                        .or_default()
                        .insert(*source);
                }
            }
        }
        let mut declarations = BTreeSet::new();
        let mut static_parameters = BTreeMap::<_, BTreeSet<_>>::new();
        for (index, function) in self.facts.functions.iter().enumerate() {
            origin_work(work, 1)?;
            let Some(statement) = function.hir_id.and_then(|id| hir.statement(id)) else {
                continue;
            };
            let crate::hir::nodes::StmtKind::Function(original) = &statement.kind else {
                continue;
            };
            if let Some(&id) = function.lexical.get(&function.syntax.name)
                && let Some(binding) = self.facts.bindings.get(id)
                && binding.name == original.name
                && binding.value.callables == [Callable::Named(index)]
                && binding.owner == function.owner.unwrap_or(ScopeId(0))
                && binding.lexical_scope == function.lexical_scope
                && binding.context.owner == function.lexical_owner.or(Some(CallableOwner::Global))
            {
                origin_work(work, 1)?;
                declarations.insert(id);
            }
            if original.body.is_none() {
                origin_work(work, original.generics.len())?;
                for generic in &original.generics {
                    let generic = hir
                        .generic(*generic)
                        .ok_or("static binding generic origin is absent")?;
                    origin_work(work, 1 + generic.name.len().div_ceil(32))?;
                    static_parameters
                        .entry(CallableOwner::Function(function.definition))
                        .or_default()
                        .insert(generic.name.clone());
                }
            }
        }
        // source_sites has already independently checked each generated recipe,
        // its actual operand tokens, the capture IDs and their receiver frame.
        let mut generated = BTreeSet::new();
        for source in &self.facts.generated_sources {
            origin_work(work, 1 + source.captures.len())?;
            generated.extend(source.captures.iter().map(|capture| capture.binding));
        }
        let mut receiving_rows = BTreeMap::new();
        origin_work(work, self.facts.binding_sources.len())?;
        for row in &self.facts.binding_sources {
            require(
                receiving_rows.insert(row.binding, row).is_none(),
                "binding birth has duplicate receiving rows",
            )?;
        }
        let mut births = BTreeSet::new();
        for (id, binding) in self
            .facts
            .bindings
            .iter()
            .enumerate()
            .filter(|(_, binding)| !binding.parameter)
        {
            origin_work(work, 1 + binding.name.len().div_ceil(32))?;
            if let Some(pattern) = binding.pattern {
                let birth = binding
                    .birth
                    .ok_or("binding lost its actual birth occurrence")?;
                require(
                    births.insert((pattern, birth, binding.name.as_str())),
                    "two bindings borrowed one original receiver birth",
                )?;
                let activation = self
                    .facts
                    .activations
                    .get(birth.activation.0 as usize)
                    .ok_or("binding birth activation is absent")?;
                require(
                    activation.id == birth.activation
                        && activation.source == Some(birth.source)
                        && activation.result.is_some(),
                    "binding birth lost its actual HIR occurrence",
                )?;
                let role = self
                    .storage_birth_role(activation, declaration_inputs, work)?
                    .ok_or(
                        "binding birth is not an initializer or an independently received answer",
                    )?;
                require(
                    self.facts
                        .evaluations
                        .get(activation.result.unwrap().0 as usize)
                        .is_some_and(|record| {
                            record.identity == Some(birth)
                                && record.scope == activation.scope
                                && record.context == activation.context
                        }),
                    "binding birth borrowed another physical result",
                )?;
                let same_frame =
                    activation.scope == binding.owner && activation.context == binding.context;
                let storage = binding
                    .context
                    .owner
                    .and_then(|owner| introduced.get(&(owner, birth.source)))
                    .and_then(|patterns| patterns.get(&pattern))
                    .is_some_and(|names| names.contains(&binding.name))
                    && same_frame;
                let sources = aliases
                    .get(&pattern)
                    .and_then(|names| names.get(&binding.name));
                origin_work(work, sources.map_or(0, BTreeSet::len))?;
                let alias = sources.is_some_and(|sources| sources.contains(&birth.source))
                    && same_frame
                    && role == StorageBirthRole::Expression;
                require(
                    storage || alias || self.storage_resource_lease_origin(id, pattern, work)?,
                    "binding introducer is not its actual storage, pattern or generated receiver role",
                )?;
                if storage {
                    let row = receiving_rows
                        .get(&id)
                        .ok_or("an actual binding lost its immutable storage source")?;
                    require(
                        row.initializer.expression == activation.result.unwrap().0 as usize
                            && row.activation == binding.owner
                            && row.context == binding.context,
                        "storage receipt borrowed another actual binding birth",
                    )?;
                }
            } else {
                let static_parameter = binding
                    .context
                    .owner
                    .and_then(|owner| static_parameters.get(&owner))
                    .is_some_and(|names| names.contains(&binding.name))
                    && binding.context.invocation.is_none()
                    && binding.context.closure_invocation.is_none()
                    && self.facts.scopes.get(&binding.owner).is_some_and(|scope| {
                        matches!(scope.origin, crate::sema::scopes::ScopeOrigin::Unresolved)
                    });
                require(
                    binding.birth.is_none()
                        && (declarations.contains(&id)
                            || generated.contains(&id)
                            || static_parameter),
                    "an actual binding lost its original HIR introducer",
                )?;
            }
        }
        Ok(())
    }

    pub(super) fn storage_binding_source_key_if_known(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        observation: Option<usize>,
    ) -> Option<Check<Option<ArgumentKey>>> {
        self.storage_binding_source_schema(expression, value, context, observation, SourceRead::Raw)
            .map(|result| {
                result?
                    .map(|(schema, _)| {
                        schema.key().map_err(|error| {
                            format!("storage path has no legacy Source export: {error}")
                        })
                    })
                    .transpose()
            })
    }

    fn storage_binding_source_schema(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        observation: Option<usize>,
        view: SourceRead,
    ) -> Option<
        Check<
            Option<(
                crate::sema::source_types::SourceSchema,
                crate::sema::context::FrozenEnvironment,
            )>,
        >,
    > {
        if value.sources.len() != 1 {
            return None;
        }
        let id = *value.sources.first()?;
        let rows: Vec<_> = self
            .facts
            .binding_sources
            .iter()
            .filter(|row| row.binding == id)
            .collect();
        let named_parameter = self.facts.bindings.get(id).is_some_and(|binding| {
            binding.parameter
                && self.facts.scopes.get(&binding.owner).is_some_and(|scope| {
                    matches!(scope.origin, crate::sema::scopes::ScopeOrigin::Named(_))
                })
        });
        if rows.is_empty() && !named_parameter {
            return None;
        }
        let source = expression.hir_id?;
        let hir = self.facts.semantic_hir.as_deref()?;
        let mut work = crate::sema::source_types::WorkLimit::new(16384);
        let plan = match projection_receipts::projection_path(hir, source, &mut work) {
            Ok(Some(plan)) => plan,
            Ok(None) => return None,
            Err(error) => return Some(Err(error.to_string())),
        };
        if named_parameter {
            let projected = (|| -> Check<_> {
                let root =
                    self.original_source_root(expression, value, context, observation, &mut 4096)?;
                let read = self
                    .facts
                    .evaluations
                    .get(root)
                    .ok_or("parameter Source read is absent")?;
                let projection = ProjectionReceipts::from_facts(self.facts)
                    .project(
                        &plan,
                        ProjectionOccurrence {
                            identity: read
                                .identity
                                .ok_or("parameter Source has no original occurrence")?,
                            context,
                            cause: value.cause,
                        },
                        view,
                        &mut work,
                    )
                    .map_err(|error| error.to_string())?;
                let mut root_ast = expression;
                for _ in 0..128 {
                    work.charge(1).map_err(|error| error.to_string())?;
                    if root_ast.hir_id == Some(plan.root()) {
                        break;
                    }
                    root_ast = match &root_ast.kind {
                        ExprKind::Field { base, .. }
                        | ExprKind::Index { base, .. }
                        | ExprKind::ComputedField { base, .. } => base,
                        _ => return Err("parameter Source path lost its original Name".into()),
                    };
                }
                require(
                    root_ast.hir_id == Some(plan.root()),
                    "parameter Source root exceeds its bound",
                )?;
                let Some((schema, environment)) = self.parameter_declaration_schema(
                    root_ast,
                    id,
                    context,
                    projection.root.0 as usize,
                    &mut work,
                )?
                else {
                    return Ok(None);
                };
                Ok(schema
                    .project_steps_if_structural(&projection.steps, &mut work)
                    .map_err(|error| error.to_string())?
                    .map(|schema| (schema, environment)))
            })();
            return match projected {
                Ok(None) => None,
                other => Some(other),
            };
        }
        let original = (|| {
            require(
                rows.len() == 1,
                "storage Name has duplicate declaration sources",
            )?;
            let binding = self
                .facts
                .bindings
                .get(id)
                .ok_or("storage Name binding is absent")?;
            require(
                binding.name == plan.name(),
                "storage source borrowed another named binding",
            )?;
            let root =
                self.original_source_root(expression, value, context, observation, &mut 4096)?;
            let read = self
                .facts
                .evaluations
                .get(root)
                .ok_or("storage read lost its actual scope")?;
            require(
                (read.scope == rows[0].activation && context == rows[0].context)
                    || self.storage_captured_binding(
                        context,
                        read.scope,
                        plan.name(),
                        id,
                        rows[0],
                    )?,
                "storage input borrowed a binding from another lexical activation",
            )?;
            require(
                self.facts.source_types.contains_binding(id)
                    && self.facts.source_types.binding_environment(id)
                        == Some(binding.typing_environment.id()),
                "storage source index differs from the original binding view",
            )?;
            let Some((schema, environment)) = self
                .facts
                .source_types
                .binding_schema_if_known(id, None, &mut work)
                .map_err(|error| error.to_string())?
            else {
                return Ok(None);
            };
            let projection = ProjectionReceipts::from_facts(self.facts)
                .project(
                    &plan,
                    ProjectionOccurrence {
                        identity: read
                            .identity
                            .ok_or("storage read has no original occurrence")?,
                        context,
                        cause: value.cause,
                    },
                    view,
                    &mut work,
                )
                .map_err(|error| error.to_string())?;
            require(
                self.facts
                    .expressions
                    .get(projection.root.0 as usize)
                    .is_some_and(|fact| {
                        fact.source_id == Some(plan.root())
                            && fact.value.sources == BTreeSet::from([id])
                    }),
                "storage path root borrowed another binding",
            )?;
            Ok(Some((schema, environment, projection.steps)))
        })();
        match original {
            Ok(Some((schema, environment, path))) => {
                match schema.project_steps_if_structural(&path, &mut work) {
                    Ok(None) => None,
                    Ok(Some(projected)) => Some(Ok(Some((projected, environment)))),
                    Err(error) => Some(Err(error.to_string())),
                }
            }
            Ok(None) => Some(Ok(None)),
            Err(error) => Some(Err(error)),
        }
    }

    fn storage_observation(
        &self,
        observed: StorageObservation,
        syntax: &Expr,
        context: InvocationContext,
        activation: ScopeId,
    ) -> Check<&Value> {
        let original = self
            .facts
            .expressions
            .get(observed.expression)
            .ok_or_else(|| "storage operand observation is outside its arena".to_owned())?;
        require(
            original.source_id.is_some()
                && original.source_id == syntax.hir_id
                && original.allocation_epoch == observed.allocation_epoch
                && self
                    .facts
                    .evaluations
                    .get(observed.expression)
                    .is_some_and(|record| {
                        record.id.0 as usize == observed.expression
                            && record.scope == activation
                            && record.context == context
                            && record.allocation_epoch == observed.allocation_epoch
                            && record
                                .identity
                                .is_some_and(|identity| Some(identity.source) == syntax.hir_id)
                    })
                && observed.allocation_epoch <= self.facts.allocation_history.len()
                && self
                    .observations
                    .row(observed.expression, &mut 4096)?
                    .context
                    == context,
            "storage operand belongs to another syntax, epoch or full invocation context",
        )?;
        Ok(&original.value)
    }

    /// Reconstruct only the guaranteed member from the genuine Type UID's
    /// source declaration. A bound never supplies a closed view of its parent
    /// or an access permission; those obligations belong to separate replay.
    fn storage_projection_source_key(
        &self,
        source: &ArgumentKey,
        slot: &Slot,
        context: InvocationContext,
    ) -> Check<Option<ArgumentKey>> {
        let (
            ArgumentKey::Binder {
                identity,
                sort: StaticBinderSort::Type,
            },
            Slot::Field(label),
        ) = (source, slot)
        else {
            return Ok(crate::sema::source_types::declarations::project(
                source,
                std::slice::from_ref(slot),
                self.facts
                    .semantic_hir
                    .as_deref()
                    .ok_or_else(|| "storage declaration has no canonical HIR".to_owned())?,
                &mut crate::sema::source_types::WorkLimit::new(4096),
            )
            .ok());
        };
        self.type_binder(identity)?;
        let binder = &self.facts.generic_binders[identity];
        let declaration = self.function(binder.definition)?;
        let parameter = declaration
            .syntax
            .generics
            .get(binder.index as usize)
            .ok_or_else(|| "storage bound UID has no source parameter".to_owned())?;
        let Some(TypeExpr {
            kind: TypeKind::Record { fields, .. },
            ..
        }) = parameter.bound.as_ref()
        else {
            return Err("storage Type UID has no declared record constraint".into());
        };
        let declared: Vec<_> = fields.iter().filter(|field| field.name == *label).collect();
        let [declared] = declared.as_slice() else {
            return Err(
                "storage member is not uniquely guaranteed by its source constraint".into(),
            );
        };
        let bound = self
            .bounds
            .get(&(binder.definition, binder.index))
            .ok_or_else(|| "storage bound UID lost its registered declaration".to_owned())?;
        let scope = self.scope(binder.definition)?;
        require(
            bound.binder == *identity && bound.scope == scope,
            "storage member borrowed a different bound UID or declaration environment",
        )?;
        let recorded: Vec<_> = bound
            .fields
            .iter()
            .filter(|field| field.label == *label)
            .collect();
        let [recorded] = recorded.as_slice() else {
            return Err("storage member lost its unique recorded declaration".into());
        };
        let key = self.normalized_key(&declared.ty, &scope)?;
        require(
            recorded.mutable == declared.mutable
                && recorded.key == key
                && self.normalized_key(&recorded.syntax, &scope)? == key,
            "storage member changed the complete Source of its declared field",
        )?;
        let named = match context.owner {
            Some(CallableOwner::Function(owner)) => {
                let id = context
                    .invocation
                    .ok_or_else(|| "storage bound field has no actual named instance".to_owned())?;
                let call = self
                    .facts
                    .copy_invocations
                    .get(id.0 as usize)
                    .ok_or_else(|| "storage bound field instance is absent".to_owned())?;
                require(
                    call.id == id && call.target == owner,
                    "storage bound field borrowed another named instance",
                )?;
                Some(call)
            }
            Some(CallableOwner::Lambda(site)) => {
                let invocation = context
                    .closure_invocation
                    .and_then(|id| {
                        self.facts
                            .closure_invocations
                            .get(id.0 as usize)
                            .filter(|call| call.id == id)
                    })
                    .ok_or_else(|| "storage bound field has no actual lambda entry".to_owned())?;
                let closure = self
                    .facts
                    .closures
                    .get(invocation.closure)
                    .filter(|closure| {
                        closure.site == Some(site) && context.closure == Some(invocation.closure)
                    })
                    .ok_or_else(|| {
                        "storage bound field borrowed another lambda object".to_owned()
                    })?;
                closure
                    .creation_invocation
                    .map(|id| {
                        self.facts
                            .copy_invocations
                            .get(id.0 as usize)
                            .filter(|call| call.id == id)
                            .ok_or_else(|| {
                                "storage bound field lost its captured instance".to_owned()
                            })
                    })
                    .transpose()?
            }
            _ => return Err("storage bound field has no callable declaration context".into()),
        };
        let selected = named
            .map(|call| self.input_selected_keys(call))
            .transpose()?
            .unwrap_or_default();
        let selected = super::call_input_source::input_select_key(&key, &selected, 0)?;
        require(
            source_reception::complete(&selected, &mut 4096).is_some(),
            "storage declared field has incomplete selected Source coordinates",
        )?;
        Ok(Some(selected))
    }

    fn storage_activation(&self, context: InvocationContext, activation: ScopeId) -> Check {
        require(
            self.facts.scopes.contains(&activation),
            "storage activation is not allocated",
        )?;
        if self.storage_handler(context, activation)?.is_some() {
            return Ok(());
        }
        // A named call inside a closure keeps the outer closure's dynamic
        // ancestry. Its current frame is nevertheless the named activation.
        if matches!(context.owner, Some(CallableOwner::Lambda(_))) {
            let id = context
                .closure_invocation
                .ok_or_else(|| "storage lambda has no actual closure invocation".to_owned())?;
            let call = self
                .facts
                .closure_invocations
                .get(id.0 as usize)
                .filter(|call| call.id == id)
                .ok_or_else(|| "storage closure activation is absent".to_owned())?;
            return require(
                call.activation == Some(activation)
                    && context.closure == Some(call.closure)
                    && context.invocation == call.parent_named
                    && context.budget_validation == call.budget_validation
                    && self
                        .facts
                        .closures
                        .get(call.closure)
                        .is_some_and(|closure| {
                            closure.site.map(CallableOwner::Lambda) == context.owner
                        }),
                "storage closure source borrowed another activation",
            );
        }
        if let Some(CallableOwner::Function(owner)) = context.owner {
            let call = context
                .invocation
                .and_then(|id| {
                    self.facts
                        .copy_invocations
                        .get(id.0 as usize)
                        .filter(|call| call.id == id)
                })
                .ok_or_else(|| "storage named activation has no actual invocation".to_owned())?;
            return require(
                call.target == owner
                    && call.caller_activation.is_none_or(|parent| {
                        self.facts.scopes.parent(&activation) == Some(&parent)
                    })
                    && self.facts.invocations.iter().any(|summary| {
                        summary.activation == Some(activation) && summary.context == Some(context)
                    }),
                "storage named source borrowed another actual activation",
            );
        }
        require(
            context.owner == Some(CallableOwner::Global)
                && activation == ScopeId(0)
                && context.invocation.is_none()
                && context.closure.is_none()
                && context.closure_invocation.is_none()
                && context.default_use.is_none(),
            "storage source has no original global or callable activation",
        )
    }

    /// An operation frame is neither its surrounding named frame nor its
    /// surrounding closure frame. Only an actual operation/continuation receipt
    /// supplies its identity; lexical ancestry alone cannot choose an activation.
    pub(in crate::sema::record_bound_validation) fn storage_handler(
        &self,
        context: InvocationContext,
        activation: ScopeId,
    ) -> Check<Option<&HandlerFact>> {
        let Some(frame) = self.frames.operation(activation)? else {
            return Ok(None);
        };
        require(
            frame.entry.context == context,
            "storage operation receiver borrowed another full invocation context",
        )?;
        Ok(Some(frame.handler))
    }

    pub(in crate::sema::record_bound_validation) fn storage_named_environments(
        &self,
        context: InvocationContext,
    ) -> Check<Vec<&FunctionInfo>> {
        let Some(CallableOwner::Function(owner)) = context.owner else {
            return Err("storage named environment has another lexical owner".into());
        };
        let call = context
            .invocation
            .and_then(|id| {
                self.facts
                    .copy_invocations
                    .get(id.0 as usize)
                    .filter(|call| call.id == id && call.target == owner)
            })
            .ok_or_else(|| "storage environment lost its actual named invocation".to_owned())?;
        if let Some(id) = call.source_event {
            let event = self
                .facts
                .copy_call_events
                .get(id.0 as usize)
                .filter(|event| {
                    event.id == id
                        && event.parent == call.parent
                        && event.owner == call.caller_owner
                })
                .ok_or_else(|| "storage environment lost its actual calling event".to_owned())?;
            let expression = event
                .callee_expression
                .ok_or_else(|| "storage environment lost its physical callee".to_owned())?;
            let value = self
                .facts
                .expressions
                .get(expression)
                .ok_or_else(|| "storage environment callee is absent".to_owned())?;
            let callers: Vec<_> = self
                .facts
                .invocation_calls
                .iter()
                .filter(|row| row.invocation == call.id)
                .collect();
            let [caller] = callers.as_slice() else {
                return Err("storage environment caller context is not unique".into());
            };
            require(
                caller.caller_owner == call.caller_owner
                    && self
                        .observations
                        .row(expression, &mut 4096)
                        .is_ok_and(|row| {
                            row.context.owner == caller.caller_owner
                                && row.context.invocation == call.parent
                                && row.context.closure == caller.caller_closure
                                && row.context.closure_invocation
                                    == caller.caller_closure_invocation
                                && row.context.default_use == caller.default_use
                                && row.context.budget_validation == context.budget_validation
                        }),
                "storage environment callee belongs to another caller context",
            )?;
            let mut selected = Vec::new();
            for callable in &value.value.callables {
                if let Callable::Named(index) = callable {
                    let function = self.facts.functions.get(*index).ok_or_else(|| {
                        "storage environment callee targets an absent function".to_owned()
                    })?;
                    if function.definition == owner {
                        selected.push(function);
                    }
                }
            }
            require(
                !selected.is_empty(),
                "storage environment has no actual matching named target",
            )?;
            return Ok(selected);
        }
        // A declaration probe has no call expression. An implicit invocation
        // may also lack one. Keep every possible instance: their binding IDs
        // must all agree rather than borrowing one convenient same-name copy.
        let selected: Vec<_> = self
            .facts
            .functions
            .iter()
            .filter(|function| function.definition == owner)
            .collect();
        require(
            !selected.is_empty(),
            "storage environment declaration is absent",
        )?;
        Ok(selected)
    }

    fn storage_captured_binding(
        &self,
        context: InvocationContext,
        activation: ScopeId,
        name: &str,
        id: BindingId,
        declaration: &BindingSource,
    ) -> Check<bool> {
        if let Some(handler) = self.storage_handler(context, activation)? {
            return Ok(handler.lexical.get(name) == Some(&id));
        }
        match context.owner {
            Some(CallableOwner::Lambda(site)) => {
                let call = context.closure_invocation.and_then(|id| {
                    self.facts
                        .closure_invocations
                        .get(id.0 as usize)
                        .filter(|call| call.id == id)
                });
                Ok(call.is_some_and(|call| {
                    call.activation == Some(activation)
                        && context.closure == Some(call.closure)
                        && self
                            .facts
                            .closures
                            .get(call.closure)
                            .is_some_and(|closure| {
                                closure.site == Some(site)
                                    && closure.lexical.get(name) == Some(&id)
                                    && closure.captures.contains(&id)
                            })
                }))
            }
            Some(CallableOwner::Function(_)) => {
                let global = declaration.activation == ScopeId(0)
                    && declaration.context.owner == Some(CallableOwner::Global)
                    && self
                        .facts
                        .bindings
                        .get(id)
                        .is_some_and(|binding| binding.owner == ScopeId(0));
                Ok(self
                    .storage_named_environments(context)?
                    .iter()
                    .all(|function| {
                        function.lexical.get(name) == Some(&id)
                            && (global || function.captures.contains(&id))
                    }))
            }
            _ => Ok(false),
        }
    }

    fn storage_declared_schema(
        &self,
        row: &BindingSource,
        sites: &super::explicit_named::SourceSites<'_>,
        declaration: &super::explicit_named::BindingSite<'_>,
        plan: &PatternPlan,
        roots: &mut SourceRoots,
    ) -> Check<Option<crate::sema::source_types::SourceSchema>> {
        let binding = self
            .facts
            .bindings
            .get(row.binding)
            .ok_or_else(|| "storage declaration binding is absent".to_owned())?;
        require(
            !binding.parameter && binding.owner == row.activation && binding.context == row.context,
            "storage declaration borrowed a parameter or another frame",
        )?;
        self.storage_activation(row.context, row.activation)?;
        let owner = declaration.owner;
        let declaration = declaration.binding;
        require(
            row.declared == declaration.ty.is_some(),
            "storage declaration changed written/inferred origin",
        )?;
        let selected = binding
            .pattern
            .and_then(|pattern| plan.get(&pattern))
            .and_then(|names| names.get(binding.name.as_str()))
            .ok_or("storage binding does not belong to its original HIR pattern")?;
        require(
            row.path == *selected,
            "storage binding changed its declared pattern projection",
        )?;
        let initial = self.storage_observation(
            row.initializer,
            &declaration.value,
            row.context,
            row.activation,
        )?;
        require(
            initial.ty != Ty::Never && initial.sources.iter().all(|source| *source < row.binding),
            "storage initializer is abrupt or creates a forward declaration cycle",
        )?;
        let Some(path) = selected else {
            return Ok(None);
        };
        let identity = (
            row.declaration,
            row.initializer.expression,
            binding.typing_environment.id(),
        );
        if let std::collections::btree_map::Entry::Vacant(entry) = roots.entry(identity) {
            let original = if declaration.ty.is_none() {
                self.storage_binding_source_schema(
                    &declaration.value,
                    initial,
                    row.context,
                    Some(row.initializer.expression),
                    SourceRead::Received,
                )
            } else {
                None
            };
            let schema = if let Some(original) = original {
                let original = original?;
                if let Some((_, environment)) = &original {
                    require(
                        environment.id() == binding.typing_environment.id(),
                        "storage alias replaced its original frozen Source environment",
                    )?;
                }
                original.map(|(schema, _)| schema)
            } else {
                let key = if let Some(syntax) = &declaration.ty {
                    let scope = self.lambda_input_scope(owner)?;
                    let key = self.input_callable_source_key(syntax, &scope)?;
                    Some(super::call_input_source::input_select_key(
                        &key,
                        &self.binding_source_selections(binding, owner)?,
                        0,
                    )?)
                } else {
                    self.original_observed_source_key_if_known(
                        &declaration.value,
                        row.initializer.expression,
                        row.context,
                        sites,
                    )?
                };
                key.as_ref()
                    .map(|key| {
                        crate::sema::source_types::declarations::schema(
                            key,
                            self.facts
                                .semantic_hir
                                .as_deref()
                                .ok_or("storage Source has no canonical HIR")?,
                            &mut crate::sema::source_types::WorkLimit::new(16384),
                        )
                        .map_err(|error| error.to_string())
                    })
                    .transpose()?
            };
            entry.insert(schema);
        }
        roots[&identity]
            .as_ref()
            .map(|root| {
                root.project_steps(path, &mut crate::sema::source_types::WorkLimit::new(16384))
                    .map_err(|error| error.to_string())
            })
            .transpose()
    }

    pub(super) fn storage_sources(&self) -> Result<(), Failure> {
        let fallback = self
            .facts
            .source_program
            .as_ref()
            .and_then(|program| program.statements.first())
            .map(|statement| statement.span)
            .unwrap_or(Span {
                file: ril_compiler_core::source::FileId(0),
                start: 0,
                end: 0,
            });
        let run = || -> Check {
            let sites = super::explicit_named::source_sites(self.facts)?;
            require(
                self.facts.binding_sources.len() <= LIMIT
                    && self.facts.storage_writes.len() <= LIMIT,
                "storage source replay budget exhausted",
            )?;
            let mut originals = BTreeMap::new();
            let mut introduced = BTreeMap::<_, BTreeMap<_, BTreeSet<_>>>::new();
            let mut initializers = BTreeMap::new();
            let mut plan_work = 4_000_000usize;
            let declaration_inputs = self.storage_declaration_inputs(&mut plan_work)?;
            let hir = self
                .facts
                .semantic_hir
                .as_deref()
                .ok_or("storage declarations have no canonical HIR")?;
            for site in &sites.bindings {
                let Some(root) = site.binding.pattern.hir_id else {
                    return Err("storage declaration lost its original HIR root".into());
                };
                let hir = self
                    .facts
                    .semantic_hir
                    .as_deref()
                    .ok_or("storage pattern has no canonical HIR")?;
                let plan = hir
                    .pattern_bindings(root, &mut plan_work)
                    .map_err(|error| error.to_string())?;
                plan_work = plan_work
                    .checked_sub(1 + plan.len())
                    .ok_or("storage binding plan index exceeds its budget")?;
                for binding in &plan {
                    plan_work = plan_work
                        .checked_sub(binding.name.len().div_ceil(32))
                        .ok_or("storage binding name exceeds its budget")?;
                    if !site.binding.is_meta {
                        introduced
                            .entry((
                                site.owner,
                                site.binding
                                    .value
                                    .hir_id
                                    .ok_or("storage initializer lost its original HIR identity")?,
                            ))
                            .or_default()
                            .entry(binding.pattern)
                            .or_default()
                            .insert(binding.name.clone());
                    }
                }
                if !site.binding.is_meta {
                    let source = site
                        .binding
                        .value
                        .hir_id
                        .ok_or("storage initializer lost its original HIR identity")?;
                    require(
                        initializers.insert(source, (site.owner, root)).is_none(),
                        "storage initializer belongs to more than one HIR declaration",
                    )?;
                }
                plan_work = plan_work
                    .checked_sub(plan.len().saturating_mul(2))
                    .ok_or("storage projection index exceeds its work bound")?;
                let mut projections = PatternPlan::new();
                for binder in plan {
                    projections
                        .entry(binder.pattern)
                        .or_default()
                        .insert(binder.name, binder.projection);
                }
                require(
                    originals
                        .insert((site.owner, root), (site, projections))
                        .is_none(),
                    "storage declaration is not a unique original binding AST",
                )?;
            }
            // Validate all actual binding origins before any tag-based pruning
            // or optional Source-table lookup can omit a guarded obligation.
            self.storage_binding_origins(&sites, &introduced, &declaration_inputs, &mut plan_work)?;
            let mut declarations = BTreeMap::new();
            let mut roots = BTreeMap::new();
            let mut receipts = BTreeMap::<_, BTreeSet<_>>::new();
            for row in &self.facts.binding_sources {
                require(
                    declarations.insert(row.binding, row).is_none(),
                    "storage declaration was recorded twice",
                )?;
                let owner = row
                    .context
                    .owner
                    .ok_or("storage declaration lost its callable owner")?;
                let (site, plan) = originals
                    .get(&(owner, row.declaration))
                    .ok_or("storage declaration lost its original HIR binding root")?;
                let reconstructed =
                    self.storage_declared_schema(row, &sites, site, plan, &mut roots)?;
                let binding = self
                    .facts
                    .bindings
                    .get(row.binding)
                    .ok_or("storage Source view has no binding")?;
                require(
                    self.facts.source_types.validate_binding_schema(
                        row.binding,
                        reconstructed.as_ref(),
                        binding.typing_environment.id(),
                    ),
                    "storage source index lost or changed its original binding schema",
                )?;
                let introducer = binding
                    .pattern
                    .ok_or("storage receipt lost its HIR introducer")?;
                plan_work = plan_work
                    .checked_sub(2 + binding.name.len().div_ceil(32))
                    .ok_or("storage receipt index exceeds its work bound")?;
                receipts
                    .entry((
                        row.declaration,
                        row.initializer.expression,
                        row.activation,
                        row.context,
                    ))
                    .or_default()
                    .insert((introducer, binding.name.clone()));
            }
            // An actual normal initialization requires its HIR binders even
            // when an attacker deletes both receipts and optional producer IDs.
            for activation in &self.facts.activations {
                plan_work = plan_work
                    .checked_sub(1)
                    .ok_or("storage initialization coverage exceeds its work bound")?;
                let Some((owner, declaration)) = activation
                    .source
                    .and_then(|source| initializers.get(&source))
                else {
                    continue;
                };
                if activation.context.owner != Some(*owner) {
                    continue;
                }
                if self
                    .storage_birth_role(activation, &declaration_inputs, &mut plan_work)?
                    .is_none()
                {
                    continue;
                }
                let Some(result) = activation.result else {
                    continue;
                };
                if self
                    .facts
                    .expressions
                    .get(result.0 as usize)
                    .is_some_and(|fact| fact.value.ty == Ty::Never)
                {
                    continue;
                }
                let (site, plan) = &originals[&(*owner, *declaration)];
                if site.binding.fallback.is_some()
                    && !initializer_may_bind(
                        hir,
                        *declaration,
                        &self
                            .facts
                            .expressions
                            .get(result.0 as usize)
                            .ok_or("guarded initializer has no result")?
                            .value,
                        &mut plan_work,
                        0,
                    )?
                {
                    continue;
                }
                let received = receipts.get(&(
                    *declaration,
                    result.0 as usize,
                    activation.scope,
                    activation.context,
                ));
                for (pattern, names) in plan {
                    for name in names.keys() {
                        plan_work = plan_work
                            .checked_sub(1 + name.len().div_ceil(32))
                            .ok_or("storage initialization binders exceed their work bound")?;
                        require(
                            received.is_some_and(|received| {
                                received.contains(&(*pattern, name.clone()))
                            }),
                            "an actual HIR initialization lost its binding reception",
                        )?;
                    }
                }
            }
            let mut covered = BTreeSet::new();
            for write in &self.facts.storage_writes {
                require(
                    covered.insert(write.rhs.expression),
                    "storage writes borrowed one RHS occurrence twice",
                )?;
                self.storage_activation(write.context, write.activation)?;
                let originals: Vec<_> = sites
                    .assignments
                    .iter()
                    .filter(|site| {
                        Some(site.owner) == write.context.owner
                            && site.target.hir_id == Some(write.target)
                            && site.operator == write.operator
                    })
                    .collect();
                let [site] = originals.as_slice() else {
                    return Err("storage write is not an original assignment".into());
                };
                let input = self.storage_observation(
                    write.rhs,
                    site.value,
                    write.context,
                    write.activation,
                )?;
                require(
                    input.ty != Ty::Never,
                    "completed RHS storage receipt claims an abrupt expression",
                )?;
                let expected = match (&site.target.kind, &write.destination) {
                    (ExprKind::Name(name), StorageDestination::Binding(id)) => {
                        let binding = self
                            .facts
                            .bindings
                            .get(*id)
                            .ok_or_else(|| "storage target binding is absent".to_owned())?;
                        require(
                            binding.name == *name
                                && binding.mode.is_reassignable()
                                && write.completed,
                            "storage Name destination differs from its real assignable binding",
                        )?;
                        let declaration = declarations.get(id).ok_or_else(|| {
                            "storage target lost its declaration source".to_owned()
                        })?;
                        require(
                            declaration.initializer.expression < write.rhs.expression,
                            "storage target declaration is later than its write",
                        )?;
                        if binding.owner != write.activation {
                            require(
                                self.storage_captured_binding(
                                    write.context,
                                    write.activation,
                                    name,
                                    *id,
                                    declaration,
                                )?,
                                "storage target is not the actual captured lexical binding",
                            )?;
                        } else {
                            // Without a recorded target read, two simultaneously
                            // plausible same-named slots cannot prove a choice.
                            let alternatives = declarations
                                .values()
                                .filter(|candidate| {
                                    candidate.activation == write.activation
                                        && candidate.initializer.expression < write.rhs.expression
                                        && self.facts.bindings.get(candidate.binding).is_some_and(
                                            |other| {
                                                other.name == *name && other.mode.is_reassignable()
                                            },
                                        )
                                })
                                .count();
                            require(
                                alternatives == 1,
                                "storage target has ambiguous same-name declaration sources",
                            )?;
                        }
                        self.facts
                            .source_types
                            .projected_binding_key(
                                declaration.binding,
                                &[],
                                self.facts.semantic_hir.as_deref(),
                            )
                            .ok()
                    }
                    (
                        ExprKind::Field { base, field, .. },
                        StorageDestination::Projection {
                            receiver,
                            selector,
                            slot,
                        },
                    ) => {
                        require(
                            selector.is_none()
                                && *slot
                                    == field
                                        .parse()
                                        .map(Slot::Tuple)
                                        .unwrap_or_else(|_| Slot::Field(field.clone())),
                            "storage field destination changed its original projection",
                        )?;
                        self.storage_write_interval(
                            write.rhs,
                            *receiver,
                            site.value,
                            write.context,
                        )?;
                        let source = self.storage_observation(
                            *receiver,
                            base,
                            write.context,
                            write.activation,
                        )?;
                        if source.ty == Ty::Never {
                            require(
                                !write.completed && write.expected.is_none(),
                                "abrupt storage receiver claims a completed write",
                            )?;
                            continue;
                        }
                        require(
                            write.completed,
                            "normal storage field write was marked aborted",
                        )?;
                        let key = self.original_observed_source_key(
                            base,
                            receiver.expression,
                            write.context,
                            &sites,
                        )?;
                        self.storage_projection_source_key(&key, slot, write.context)?
                    }
                    (
                        ExprKind::Index { base, index, .. },
                        StorageDestination::Projection {
                            receiver,
                            selector,
                            slot,
                        },
                    ) => {
                        self.storage_write_interval(
                            write.rhs,
                            *receiver,
                            site.value,
                            write.context,
                        )?;
                        let source = self.storage_observation(
                            *receiver,
                            base,
                            write.context,
                            write.activation,
                        )?;
                        if source.ty == Ty::Never {
                            require(
                                !write.completed && selector.is_none() && write.expected.is_none(),
                                "abrupt indexed receiver claims a write",
                            )?;
                            continue;
                        }
                        let selector = selector
                            .ok_or_else(|| "storage index lost its actual selector".to_owned())?;
                        self.storage_write_interval(*receiver, selector, base, write.context)?;
                        let selected = self.storage_observation(
                            selector,
                            index,
                            write.context,
                            write.activation,
                        )?;
                        if selected.ty == Ty::Never {
                            require(
                                !write.completed && write.expected.is_none(),
                                "abrupt storage selector claims a write",
                            )?;
                            continue;
                        }
                        require(
                            write.completed,
                            "normal storage index write was marked aborted",
                        )?;
                        let key = self.original_observed_source_key(
                            base,
                            receiver.expression,
                            write.context,
                            &sites,
                        )?;
                        let expected_slot = if matches!(key, ArgumentKey::Map { .. }) {
                            Slot::AnyIndex
                        } else if let Some(Constant::Integer(index)) = selected.constant {
                            Slot::Index(index as i64)
                        } else {
                            Slot::AnyIndex
                        };
                        require(
                            *slot == expected_slot,
                            "storage index changed its actual selected slot",
                        )?;
                        if let ArgumentKey::Map { key: map_key, .. } = &key {
                            let actual = self
                                .original_observed_source_key(
                                    index,
                                    selector.expression,
                                    write.context,
                                    &sites,
                                )
                                .ok();
                            let fresh = source_reception::construction(index, &mut 4096);
                            require(
                                storage_compatible(
                                    map_key,
                                    actual.as_ref(),
                                    fresh.as_ref(),
                                    self.facts.semantic_hir.as_deref(),
                                ) == Some(true),
                                "storage map selector does not fit its original key source",
                            )?;
                        }
                        self.storage_projection_source_key(&key, slot, write.context)?
                    }
                    _ => return Err("storage write changed its real destination form".into()),
                };
                require(
                    expected == write.expected,
                    "storage write borrowed a different expected source schema",
                )?;
                let expected = expected.ok_or_else(|| {
                    "storage write has an unresolved original destination source".to_owned()
                })?;
                let actual = self
                    .original_observed_source_key(
                        site.value,
                        write.rhs.expression,
                        write.context,
                        &sites,
                    )
                    .ok();
                let fresh = source_reception::construction(site.value, &mut 4096);
                let answer = if crate::sema::source_types::key_is_coordinate_free_with_declarations(
                    &expected,
                    self.facts.semantic_hir.as_deref(),
                ) {
                    Some(true)
                } else if write.operator != "=" {
                    Some(false)
                } else {
                    storage_compatible(
                        &expected,
                        actual.as_ref(),
                        fresh.as_ref(),
                        self.facts.semantic_hir.as_deref(),
                    )
                };
                require(
                    answer == Some(true),
                    "storage original RHS does not prove the destination source coordinates",
                )?;
            }
            // Reverse coverage starts from actual RHS roots, not from a
            // supposedly complete list supplied by the write certificates.
            for site in &sites.assignments {
                for row in self
                    .facts
                    .invocation_expressions
                    .iter()
                    .filter(|row| row.context.owner == Some(site.owner))
                {
                    let value = self.facts.expressions.get(row.expression).ok_or_else(|| {
                        "storage reverse coverage expression is absent".to_owned()
                    })?;
                    if value.source_id.is_some()
                        && value.source_id == site.value.hir_id
                        && value.value.ty != Ty::Never
                    {
                        require(
                            covered.contains(&row.expression),
                            "an actual assignment lost its storage reception receipt",
                        )?;
                    }
                }
            }
            Ok(())
        };
        run().map_err(|message| (fallback, None, message))
    }

    fn storage_write_interval(
        &self,
        before: StorageObservation,
        after: StorageObservation,
        before_syntax: &Expr,
        context: InvocationContext,
    ) -> Check {
        require(
            before.expression < after.expression
                && before.allocation_epoch <= after.allocation_epoch,
            "storage operand order or allocation epochs moved backwards",
        )?;
        require(
            !self.facts.invocation_expressions.iter().any(|row| {
                row.context == context
                    && before.expression < row.expression
                    && row.expression < after.expression
                    && self
                        .facts
                        .expressions
                        .get(row.expression)
                        .is_some_and(|value| {
                            value.source_id.is_some() && value.source_id == before_syntax.hir_id
                        })
            }),
            "storage target borrowed a later repeated RHS occurrence",
        )
    }
}

pub(in crate::sema::record_bound_validation) fn storage_compatible(
    expected: &ArgumentKey,
    actual: Option<&ArgumentKey>,
    fresh: Option<&Construction>,
    hir: Option<&crate::hir::nodes::HirProgram>,
) -> Option<bool> {
    if contains_callable(expected, &mut 4096)? {
        return None;
    }
    if crate::sema::source_types::key_is_coordinate_free_with_declarations(expected, hir) {
        return Some(true);
    }
    if let Some(actual) = actual {
        return source_reception::compatible(expected, actual, fresh, &mut 4096);
    }
    source_reception::empty_context(expected, fresh?, &mut 4096)
}

fn contains_callable(key: &ArgumentKey, work: &mut usize) -> Option<bool> {
    *work = work.checked_sub(1)?;
    let children: Vec<&ArgumentKey> = match key {
        ArgumentKey::Callable { .. } | ArgumentKey::GenericBuiltin(_) => return Some(true),
        ArgumentKey::Array { element, .. } => vec![element],
        ArgumentKey::Map { key, value } => vec![key, value],
        ArgumentKey::Name { arguments, .. } | ArgumentKey::Tuple(arguments) => {
            arguments.iter().collect()
        }
        ArgumentKey::Record { fields, row } => fields
            .iter()
            .map(|field| &field.2)
            .chain(row.iter().map(|row| row.as_ref()))
            .collect(),
        ArgumentKey::Closed(_) => return None,
        ArgumentKey::Binder { .. } => vec![],
    };
    for child in children {
        if contains_callable(child, work)? {
            return Some(true);
        }
    }
    Some(false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::{
        copy_contract::{
            CopyCallEvent, CopyCallEventId, CopyInvocation, CopyInvocationStatus, CopyValueSnapshot,
        },
        copy_templates::InstanceId,
        effect_identity::{
            ClosureInvocation, ClosureInvocationId, InvocationCall, InvocationExpression,
        },
        facts::{LoanId, NodeId, RootId},
        model::{BindingInfo, ClosureInfo},
        summary::InvocationSummary,
    };
    use ril_compiler_core::{ids::ClosureSiteId, source::FileId};
    use ril_syntax::ast::{BindingMode, Function};

    fn span() -> Span {
        Span {
            file: FileId(0),
            start: 0,
            end: 1,
        }
    }
    fn context(owner: CallableOwner) -> InvocationContext {
        InvocationContext {
            invocation: None,
            owner: Some(owner),
            closure: None,
            closure_invocation: None,
            budget_validation: false,
            default_use: None,
        }
    }
    fn function(binding: BindingId) -> FunctionInfo {
        FunctionInfo {
            hir_id: None,
            definition: DefinitionId(0),
            lexical_owner: Some(CallableOwner::Global),
            typing_environment: Default::default(),
            syntax: Function {
                visibility: Visibility::Private,
                is_meta: false,
                is_halt: false,
                name: "work".into(),
                generics: vec![],
                parameters: vec![],
                return_type: None,
                annotations: vec![],
                signature_where: vec![],
                body: None,
                span: span(),
            },
            lexical: [("counter".into(), binding)].into(),
            owner: None,
            handler_context: vec![],
            lexical_scope: 0,
            environment: None,
            captures: BTreeSet::new(),
            writes: BTreeSet::new(),
            environment_published: false,
        }
    }
    fn binding(id: BindingId) -> BindingInfo {
        BindingInfo {
            pattern: None,
            birth: None,
            context: context(CallableOwner::Global),
            typing_environment: Default::default(),
            name: "counter".into(),
            value: Value::scalar(Ty::Int("int".into()), None, CauseId(0)),
            mode: BindingMode::Var,
            owner: ScopeId(0),
            lexical_scope: 0,
            span: span(),
            root: RootId(id as u32),
            cell: None,
            alive: true,
            slot_used: true,
            write_used: false,
            used: true,
            forwarded: BTreeSet::new(),
            parameter: false,
        }
    }
    fn source(id: BindingId) -> BindingSource {
        BindingSource {
            binding: id,
            context: context(CallableOwner::Global),
            activation: ScopeId(0),
            declaration: ril_compiler_core::ids::PatternId(0),
            declared: false,
            initializer: StorageObservation {
                expression: 0,
                allocation_epoch: 0,
            },
            path: Some(vec![]),
        }
    }
    fn model() -> (SemanticFacts, InvocationContext) {
        let mut facts = SemanticFacts::default();
        let mut current = context(CallableOwner::Function(DefinitionId(0)));
        current.invocation = Some(InstanceId(0));
        facts
            .scopes
            .extend([ScopeId(0), ScopeId(10), ScopeId(20), ScopeId(30)]);
        facts.scopes.set_parent(ScopeId(20), ScopeId(0));
        facts.functions = vec![function(0), function(1)];
        facts.bindings = vec![binding(0), binding(1)];
        facts.copy_invocations.push(CopyInvocation {
            id: InstanceId(0),
            entry: crate::sema::application_effect::CallableEntry {
                parent: None,
                caller_context: context(CallableOwner::Global),
                origin: crate::sema::application_effect::EntryOrigin::Unresolved,
                allocation_epoch: 0,
                arguments: vec![],
            },
            parent: None,
            caller: None,
            caller_owner: Some(CallableOwner::Global),
            caller_activation: Some(ScopeId(0)),
            target: DefinitionId(0),
            span: span(),
            declaration_probe: false,
            direct: true,
            source_event: Some(CopyCallEventId(0)),
            boundaries: BTreeSet::new(),
            result: None,
            resource_copies: vec![],
            status: CopyInvocationStatus::Completed,
        });
        let mut callee = Value::scalar(Ty::Unknown, None, CauseId(0));
        callee.callables.push(Callable::Named(1));
        facts.expressions.push(crate::sema::ExpressionFact {
            allocation_epoch: 0,
            source_id: None,
            span: span(),
            value: callee,
        });
        facts.invocation_expressions.push(InvocationExpression {
            context: context(CallableOwner::Global),
            expression: 0,
            argument_of: None,
        });
        facts.invocation_calls.push(InvocationCall {
            invocation: InstanceId(0),
            caller_owner: Some(CallableOwner::Global),
            caller_closure: None,
            caller_closure_invocation: None,
            default_use: None,
        });
        facts.copy_call_events.push(CopyCallEvent {
            source_id: None,
            id: CopyCallEventId(0),
            callee_expression: Some(0),
            result_expression: None,
            owner: Some(CallableOwner::Global),
            parent: None,
            span: span(),
            target: Some(DefinitionId(0)),
            direct: true,
            copy_operation: None,
            references: vec![],
        });
        facts.invocations.push(InvocationSummary {
            activation: Some(ScopeId(20)),
            context: Some(current),
            ..Default::default()
        });
        (facts, current)
    }
    fn replay(facts: &SemanticFacts) -> Replay<'_> {
        Replay {
            facts,
            frames: crate::sema::scopes::FrameIndex::new(facts).unwrap(),
            blocks: None,
            observations: super::super::observation_index::ObservationIndex::new(facts).unwrap(),
            functions: BTreeMap::new(),
            bounds: BTreeMap::new(),
            parameter_sources: BTreeMap::new(),
        }
    }

    #[test]
    fn current_named_activation_is_not_its_retained_outer_closure_context() {
        let (mut facts, mut current) = model();
        current.closure = Some(0);
        current.closure_invocation = Some(ClosureInvocationId(0));
        facts.invocations[0].context = Some(current);
        facts.closures.push(ClosureInfo {
            contract: std::sync::Arc::new(crate::sema::model::LambdaContract {
                source: None,
                return_type: None,
                annotations: vec![],
                span: span(),
                typing_environment: Default::default(),
            }),
            hir_id: None,
            site: Some(ClosureSiteId(0)),
            creation_invocation: None,
            creation_closure: None,
            creation_default: None,
            handler_context: vec![],
            parameters: vec![],
            body: Expr {
                hir_id: None,
                kind: ExprKind::Error,
                span: span(),
            },
            lexical: BTreeMap::new(),
            captures: BTreeSet::new(),
            writes: BTreeSet::new(),
            owner: ScopeId(0),
            node: NodeId(0),
        });
        facts.closure_invocations.push(ClosureInvocation {
            id: ClosureInvocationId(0),
            entry: crate::sema::application_effect::CallableEntry {
                parent: None,
                caller_context: current,
                origin: crate::sema::application_effect::EntryOrigin::Unresolved,
                allocation_epoch: 0,
                arguments: std::sync::Arc::new(vec![]),
            },
            source_event: None,
            caller_activation: ScopeId(0),
            activation: Some(ScopeId(10)),
            closure: 0,
            parent_named: Some(InstanceId(0)),
            parent_closure: None,
            caller_owner: Some(CallableOwner::Global),
            site: span(),
            probe: false,
            budget_validation: false,
            status: CopyInvocationStatus::Completed,
        });
        assert!(
            replay(&facts)
                .storage_activation(current, ScopeId(20))
                .is_ok()
        );
        assert!(
            replay(&facts)
                .storage_activation(current, ScopeId(10))
                .is_err()
        );
        current.owner = Some(CallableOwner::Lambda(ClosureSiteId(0)));
        assert!(
            replay(&facts)
                .storage_activation(current, ScopeId(10))
                .is_ok()
        );
        assert!(
            replay(&facts)
                .storage_activation(current, ScopeId(20))
                .is_err()
        );
    }

    #[test]
    fn ambient_globals_and_retained_locals_use_the_actual_named_callee_binding_ids() {
        let (mut facts, current) = model();
        assert!(
            replay(&facts)
                .storage_captured_binding(current, ScopeId(20), "counter", 1, &source(1))
                .unwrap()
        );
        assert!(
            !replay(&facts)
                .storage_captured_binding(current, ScopeId(20), "counter", 0, &source(0))
                .unwrap()
        );
        facts.bindings[1].owner = ScopeId(10);
        let mut local = source(1);
        local.activation = ScopeId(10);
        local.context = current;
        assert!(
            !replay(&facts)
                .storage_captured_binding(current, ScopeId(20), "counter", 1, &local)
                .unwrap()
        );
        facts.functions[1].captures.insert(1);
        assert!(
            replay(&facts)
                .storage_captured_binding(current, ScopeId(20), "counter", 1, &local)
                .unwrap()
        );
        // Without a physical callee no convenient same-definition copy can
        // select the environment; all remaining candidates must agree.
        facts.copy_invocations[0].source_event = None;
        assert!(
            !replay(&facts)
                .storage_captured_binding(current, ScopeId(20), "counter", 1, &local)
                .unwrap()
        );
        facts.functions[0].lexical.insert("counter".into(), 1);
        facts.functions[0].captures.insert(1);
        assert!(
            replay(&facts)
                .storage_captured_binding(current, ScopeId(20), "counter", 1, &local)
                .unwrap()
        );
    }

    #[test]
    fn operation_loans_cannot_invent_a_missing_receiver_frame() {
        let (mut facts, current) = model();
        facts.handlers.push(HandlerFact {
            typing_environment: Default::default(),
            site: None,
            callable_owner: current.owner,
            id: 0,
            boundary: 4,
            span: span(),
            operations: vec![7],
            arm_spans: vec![],
            lexical: [("counter".into(), 1)].into(),
            answer: None,
            arms: vec![],
            outer: vec![],
        });
        facts
            .operation_loan_starts
            .push(crate::sema::resumption::OperationLoanStart {
                loan: LoanId(0),
                activation: ScopeId(30),
                boundary: 4,
                handler: 0,
                operation: 7,
                parameter: 0,
                temporary: true,
                context: current,
                source: CopyValueSnapshot {
                    value: Value::scalar(Ty::Unit, None, CauseId(0)),
                    nodes: vec![],
                    relations: vec![],
                },
                allocation_epoch: 0,
                span: span(),
                cause: CauseId(0),
            });
        assert!(
            replay(&facts)
                .storage_activation(current, ScopeId(30))
                .is_err()
        );
        assert!(
            replay(&facts)
                .storage_handler(current, ScopeId(30))
                .unwrap()
                .is_none()
        );
        let mut foreign = current;
        foreign.invocation = Some(InstanceId(99));
        assert!(
            replay(&facts)
                .storage_activation(foreign, ScopeId(30))
                .is_err()
        );
        facts.operation_loan_starts[0].operation = 8;
        assert!(
            replay(&facts)
                .storage_activation(current, ScopeId(30))
                .is_err()
        );
    }
}
