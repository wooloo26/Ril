//! Closed invocation selection. No source span supplies a substitution proof.
use super::*;
use crate::sema::{
    SemanticFacts,
    copy_contract::CopyInvocationStatus,
    copy_templates::InstanceId,
    effect_identity::{ArgumentKey, InvocationWitnessKind, StaticArgumentWitness},
    model::Callable,
};
use ril_ir::specialization as irs;
use std::collections::{BTreeMap, BTreeSet};
mod closures;
mod defaults;

type Site = (u32, u32, u32);
fn site(span: Span) -> Site {
    (span.file.0, span.start, span.end)
}

#[derive(Default)]
pub(super) struct Plan {
    pub instances: Vec<Instance>,
    pub templates: BTreeSet<DefinitionId>,
    calls: BTreeMap<InstanceId, usize>,
    names: BTreeSet<String>,
}
pub(super) struct Instance {
    pub record: irs::Instance,
    pub representative: InstanceId,
    pub operations: BTreeMap<Site, u64>,
    closures: BTreeMap<ril_compiler_core::ids::ClosureSiteId, closures::ClosurePlan>,
    defaults: BTreeMap<u32, defaults::DefaultPlan>,
}

#[derive(Clone, Copy)]
enum Selection {
    Named(InstanceId, CallableOwner),
    Default(crate::sema::default_uses::DefaultUseId, CallableOwner),
    Closure(
        crate::sema::effect_identity::ClosureInvocationId,
        CallableOwner,
    ),
}
impl Selection {
    fn owner(self) -> CallableOwner {
        match self {
            Self::Named(_, owner) | Self::Closure(_, owner) | Self::Default(_, owner) => owner,
        }
    }
    fn matches(
        self,
        context: crate::sema::effect_identity::InvocationContext,
        facts: &SemanticFacts,
    ) -> bool {
        context.owner == Some(self.owner())
            && match self {
                Self::Named(id, _) => {
                    context.invocation == Some(id)
                        && !context.default_use.is_some_and(|default| {
                            let usage = &facts.default_uses[default.0 as usize];
                            usage.owner == context.owner
                                && usage.caller.invocation == context.invocation
                                && usage.caller.closure_invocation == context.closure_invocation
                        })
                }
                Self::Default(id, _) => {
                    let usage = &facts.default_uses[id.0 as usize];
                    context.default_use == Some(id)
                        && context.invocation == usage.caller.invocation
                        && context.closure_invocation == usage.caller.closure_invocation
                }
                Self::Closure(id, _) => context.closure_invocation == Some(id),
            }
    }
}

fn key(value: &ArgumentKey) -> Result<irs::ArgumentKey, NotImplemented> {
    crate::type_identity_lower::closed_key(value)
}
fn argument(value: &StaticArgumentWitness) -> Result<irs::Argument, NotImplemented> {
    if value.syntax.is_none() {
        return Err(unsupported(
            "native specialization is missing its complete static type witness",
        ));
    }
    Ok(irs::Argument {
        definition: value.definition,
        index: value.index,
        key: key(value.key.as_ref().ok_or_else(|| {
            unsupported("native specialization has an unresolved static argument")
        })?)?,
    })
}
fn binders(value: &ArgumentKey, output: &mut BTreeSet<String>) {
    match value {
        ArgumentKey::Binder { identity, .. } => {
            output.insert(identity.clone());
        }
        ArgumentKey::Closed(_) | ArgumentKey::GenericBuiltin(_) => {}
        ArgumentKey::Name { arguments, .. } | ArgumentKey::Tuple(arguments) => {
            for value in arguments {
                binders(value, output);
            }
        }
        ArgumentKey::Array { element, .. } => binders(element, output),
        ArgumentKey::Map { key, value } => {
            binders(key, output);
            binders(value, output);
        }
        ArgumentKey::Record { fields, row } => {
            for (_, _, value) in fields {
                binders(value, output);
            }
            if let Some(row) = row {
                binders(row, output);
            }
        }
        ArgumentKey::Callable {
            parameters, result, ..
        } => {
            for (_, value) in parameters {
                binders(value, output);
            }
            binders(result, output);
        }
    }
}

fn operation_map(
    facts: &SemanticFacts,
    selection: Selection,
) -> Result<BTreeMap<Site, u64>, NotImplemented> {
    let mut output = BTreeMap::new();
    for observation in &facts.invocation_expressions {
        if !selection.matches(observation.context, facts) {
            continue;
        }
        let fact = facts
            .expressions
            .get(observation.expression)
            .ok_or_else(|| {
                unsupported("native specialization references a missing expression witness")
            })?;
        if let [Callable::Builtin(name)] = fact.value.callables.as_slice()
            && let Some(operation) = facts.operations.get(name)
            && output
                .insert(site(fact.span), operation.identity)
                .is_some_and(|previous| previous != operation.identity)
        {
            return Err(unsupported(
                "one invocation selects different effect identities at one lexical site",
            ));
        }
    }
    Ok(output)
}

impl Plan {
    pub fn new(program: &crate::hir::VerifiedProgram) -> Result<Self, NotImplemented> {
        let facts = program.facts();
        let mut names = BTreeSet::new();
        for effect in &facts.effect_instances {
            for value in &effect.key.arguments {
                binders(value, &mut names);
            }
        }
        let mut plan = Self::default();
        for name in names {
            let binder = facts.generic_binders.get(&name).ok_or_else(|| {
                unsupported("symbolic effect instance has no canonical binder owner")
            })?;
            plan.templates.insert(binder.definition);
        }
        if plan.templates.is_empty() {
            return Ok(plan);
        }
        let mut next = program
            .definitions()
            .iter()
            .map(|definition| definition.id.0)
            .chain(facts.functions.iter().map(|info| info.definition.0))
            .max()
            .unwrap_or(0)
            .checked_add(1)
            .ok_or_else(|| unsupported("native specialization definition identity exhausted"))?;
        for &definition in &plan.templates {
            let info = facts
                .functions
                .iter()
                .find(|info| info.definition == definition)
                .ok_or_else(|| {
                    unsupported("effect specialization template declaration is missing")
                })?;
            if info.syntax.body.is_none()
                || !matches!(info.lexical_owner, None | Some(CallableOwner::Global))
            {
                return Err(unsupported(
                    "effect specialization requires its nested declaration environment mapping",
                ));
            }
            plan.names.insert(info.syntax.name.clone());
        }
        for observed in &facts.effect_invocations {
            if !plan.templates.contains(&observed.function) {
                continue;
            }
            let Some(invocation) = observed.invocation else {
                return Err(unsupported(
                    "effect specialization lacks a real named invocation identity",
                ));
            };
            let call = facts
                .copy_invocations
                .get(invocation.0 as usize)
                .filter(|call| call.id == invocation && call.target == observed.function)
                .ok_or_else(|| {
                    unsupported("effect specialization invocation does not match its named call")
                })?;
            let closed = observed
                .arguments
                .iter()
                .chain(&observed.captured_arguments)
                .all(|argument| argument.key.as_ref().is_some_and(ArgumentKey::is_closed));
            if !closed {
                continue;
            }
            if call.status != CopyInvocationStatus::Completed
                || !observed.unresolved.is_empty()
                || !observed.unresolved_captured_binders.is_empty()
            {
                return Err(unsupported(
                    "effect specialization needs a completed call and all callback dependencies",
                ));
            }
            if !observed.captured_arguments.is_empty() || !observed.callbacks.is_empty() {
                return Err(unsupported(
                    "effect specialization callback and captured-binder dependencies require complete owner mapping",
                ));
            }
            let arguments = observed
                .arguments
                .iter()
                .map(argument)
                .collect::<Result<Vec<_>, _>>()?;
            let info = facts
                .functions
                .iter()
                .find(|info| info.definition == observed.function)
                .unwrap();
            if arguments.len() != info.syntax.generics.len()
                || arguments.iter().enumerate().any(|(index, arg)| {
                    arg.definition != observed.function || arg.index != index as u32
                })
            {
                return Err(unsupported(
                    "effect specialization static argument coverage differs from its declaration",
                ));
            }
            let operations = operation_map(
                facts,
                Selection::Named(invocation, CallableOwner::Function(observed.function)),
            )?;
            let index = if let Some(index) = plan.instances.iter().position(|instance| {
                instance.record.template == observed.function
                    && instance.record.arguments == arguments
            }) {
                if plan.instances[index].operations != operations {
                    return Err(unsupported(
                        "equal static instances have inconsistent effect operation selections",
                    ));
                }
                plan.instances[index]
                    .record
                    .invocations
                    .push(ril_ir::provenance::CopyInstanceId(invocation.0));
                index
            } else {
                let definition = DefinitionId(next);
                next = next.checked_add(1).ok_or_else(|| {
                    unsupported("native specialization definition identity exhausted")
                })?;
                let index = plan.instances.len();
                plan.instances.push(Instance {
                    record: irs::Instance {
                        template: observed.function,
                        definition,
                        name: format!("\0ril.specialized.{}", definition.0),
                        arguments,
                        captured_arguments: vec![],
                        invocations: vec![ril_ir::provenance::CopyInstanceId(invocation.0)],
                        owners: vec![irs::OwnerMap {
                            source: CallableOwner::Function(observed.function),
                            target: CallableOwner::Function(definition),
                        }],
                        handlers: vec![],
                        defaults: vec![],
                    },
                    representative: invocation,
                    operations,
                    closures: BTreeMap::new(),
                    defaults: BTreeMap::new(),
                });
                index
            };
            if plan.calls.insert(invocation, index).is_some() {
                return Err(unsupported(
                    "native specialization has duplicate invocation evidence",
                ));
            }
        }
        for &definition in &plan.templates {
            if !plan
                .instances
                .iter()
                .any(|instance| instance.record.template == definition)
            {
                return Err(unsupported(
                    "symbolic effect template has no closed native specialization",
                ));
            }
        }
        defaults::prepare(&mut plan, facts)?;
        closures::prepare(&mut plan, facts)?;
        let mut next_handler = facts
            .handlers
            .iter()
            .filter_map(|handler| handler.site)
            .map(|id| id.0)
            .max()
            .map_or(Some(0), |id| id.checked_add(1))
            .ok_or_else(|| unsupported("specialized handler identity exhausted"))?;
        for instance in &mut plan.instances {
            let sites: BTreeSet<_> = facts
                .handlers
                .iter()
                .filter(|handler| {
                    handler.callable_owner.is_some_and(|owner| {
                        instance
                            .record
                            .owners
                            .iter()
                            .any(|mapping| mapping.source == owner)
                    })
                })
                .filter_map(|handler| handler.site)
                .collect();
            for source in sites {
                let target = ril_compiler_core::ids::HandlerSiteId(next_handler);
                next_handler = next_handler
                    .checked_add(1)
                    .ok_or_else(|| unsupported("specialized handler identity exhausted"))?;
                instance
                    .record
                    .handlers
                    .push(irs::HandlerMap { source, target });
            }
        }
        // Every lexical operation observed while universally checking a template
        // must be covered in each selected instance, including unused branches.
        for instance in &plan.instances {
            let info = facts
                .functions
                .iter()
                .find(|info| info.definition == instance.record.template)
                .unwrap();
            for observation in &facts.invocation_expressions {
                if observation.context.owner
                    != Some(CallableOwner::Function(instance.record.template))
                {
                    continue;
                }
                let fact = &facts.expressions[observation.expression];
                let body = info.syntax.body.as_ref().unwrap().span;
                if fact.span.file != body.file
                    || fact.span.start < body.start
                    || fact.span.end > body.end
                {
                    continue;
                }
                if let [Callable::Builtin(name)] = fact.value.callables.as_slice()
                    && facts.operations.contains_key(name)
                    && !instance.operations.contains_key(&site(fact.span))
                {
                    return Err(unsupported(
                        "effect specialization is missing a template body operation site (including inactive branches)",
                    ));
                }
            }
        }
        Ok(plan)
    }

    pub fn next_definition(&self, fallback: u32) -> u32 {
        self.instances
            .iter()
            .map(|instance| instance.record.definition.0 + 1)
            .max()
            .unwrap_or(fallback)
            .max(fallback)
    }
    pub fn is_template_name(&self, name: &str) -> bool {
        self.names.contains(name)
    }

    pub fn call_target(
        &self,
        facts: &SemanticFacts,
        owner: Option<CallableOwner>,
        context: Option<usize>,
        default_context: Option<u32>,
        span: Span,
    ) -> Result<Option<(DefinitionId, String)>, NotImplemented> {
        self.validate_default_applications(facts, owner, context, default_context, span)?;
        let mut selected = None;
        for observed in &facts.invocation_calls {
            if observed.caller_owner != owner {
                continue;
            }
            let Some(call) = facts.copy_invocations.get(observed.invocation.0 as usize) else {
                return Err(unsupported("native specialization child call is missing"));
            };
            if call.span != span || call.declaration_probe || !self.templates.contains(&call.target)
            {
                continue;
            }
            if let Some(context) = context {
                if let Some(parameter) = default_context {
                    if !observed.default_use.is_some_and(|id| {
                        self.instances[context].defaults[&parameter]
                            .uses
                            .contains(&id)
                    }) {
                        continue;
                    }
                } else if let Some(CallableOwner::Lambda(site)) = owner {
                    let Some(closure) = self.instances[context].closures.get(&site) else {
                        return Err(unsupported(
                            "specialized caller closure has no invocation partition",
                        ));
                    };
                    if !observed
                        .caller_closure_invocation
                        .is_some_and(|call| closure.calls.contains(&call))
                    {
                        continue;
                    }
                } else {
                    let Some(parent) = call.parent else {
                        continue;
                    };
                    if !self.instances[context]
                        .record
                        .invocations
                        .iter()
                        .any(|id| id.0 == parent.0)
                    {
                        continue;
                    }
                }
            }
            let Some(&index) = self.calls.get(&call.id) else {
                return Err(unsupported(
                    "generic effect call has no closed native instance for this invocation",
                ));
            };
            if selected.is_some_and(|previous| previous != index) {
                return Err(unsupported(
                    "one unspecialized call site selects different generic effect instances",
                ));
            }
            selected = Some(index);
        }
        Ok(selected.map(|index| {
            (
                self.instances[index].record.template,
                self.instances[index].record.name.clone(),
            )
        }))
    }

    pub fn facts(
        &self,
        facts: &SemanticFacts,
        index: usize,
    ) -> Result<SemanticFacts, NotImplemented> {
        let instance = &self.instances[index];
        let selected = self.project(
            facts,
            index,
            Selection::Named(
                instance.representative,
                CallableOwner::Function(instance.record.template),
            ),
        )?;
        if selected
            .retained_handlers
            .iter()
            .any(|proof| !proof.handlers.is_empty())
        {
            return Err(unsupported(
                "specialized named retained recipes require their own instance mapping",
            ));
        }
        let expected = shape(&selected, facts)?;
        for call in &instance.record.invocations {
            if call.0 == instance.representative.0 {
                continue;
            }
            let actual = shape(
                &self.project(
                    facts,
                    index,
                    Selection::Named(
                        InstanceId(call.0),
                        CallableOwner::Function(instance.record.template),
                    ),
                )?,
                facts,
            )?;
            if actual != expected {
                return Err(unsupported(
                    "equal static instances have conflicting lowering witnesses",
                ));
            }
        }
        let declaration = &facts
            .functions
            .iter()
            .find(|info| info.definition == instance.record.template)
            .unwrap()
            .syntax;
        let present: BTreeSet<_> = selected
            .expressions
            .iter()
            .map(|fact| site(fact.span))
            .collect();
        for observed in &facts.invocation_expressions {
            if observed.context.owner != Some(CallableOwner::Function(instance.record.template)) {
                continue;
            }
            let fact = &facts.expressions[observed.expression];
            let body = declaration.body.as_ref().unwrap().span;
            if fact.span.file == body.file
                && fact.span.start >= body.start
                && fact.span.end <= body.end
                && !present.contains(&site(fact.span))
            {
                return Err(unsupported(
                    "effect specialization lacks complete emitted-expression coverage",
                ));
            }
        }
        Ok(selected)
    }

    fn project(
        &self,
        facts: &SemanticFacts,
        index: usize,
        selection: Selection,
    ) -> Result<SemanticFacts, NotImplemented> {
        let instance = &self.instances[index];
        let owner = Some(selection.owner());
        let matches = |context| selection.matches(context, facts);
        let mut selected = facts.clone();
        selected.expressions = facts
            .invocation_expressions
            .iter()
            .filter(|observation| matches(observation.context))
            .map(|observation| facts.expressions[observation.expression].clone())
            .collect();
        selected.implicit_unwraps.clear();
        selected.variant_projections.clear();
        selected.static_key_checks.clear();
        selected.budget_proofs.clear();
        selected.handlers.clear();
        selected.retained_handlers.clear();
        selected.numeric_selections.clear();
        for witness in &facts.invocation_witnesses {
            if !matches(witness.context) {
                continue;
            }
            match &witness.kind {
                InvocationWitnessKind::NumericSelection(selection) => {
                    selected.numeric_selections.push(selection.clone())
                }
                InvocationWitnessKind::ImplicitUnwrap(proof) => {
                    if selected
                        .implicit_unwraps
                        .insert(site(witness.span), proof.clone())
                        .is_some_and(|old| old.tags != proof.tags || old.depth != proof.depth)
                    {
                        return Err(unsupported(
                            "effect specialization has inconsistent implicit projections",
                        ));
                    }
                }
                InvocationWitnessKind::VariantProjection(proof) => {
                    if selected
                        .variant_projections
                        .insert(site(witness.span), proof.clone())
                        .is_some_and(|old| old.tag != proof.tag || old.direct != proof.direct)
                    {
                        return Err(unsupported(
                            "effect specialization has inconsistent variant projections",
                        ));
                    }
                }
                InvocationWitnessKind::StaticKey(index) => selected
                    .static_key_checks
                    .push(facts.static_key_checks[*index].clone()),
                InvocationWitnessKind::Budget(proof) => {
                    if proof.callee_coverage.is_empty()
                        || std::iter::once(&proof.cause)
                            .chain(&proof.callee_coverage)
                            .chain(&proof.cleanup_coverage)
                            .any(|cause| {
                                !facts
                                    .explanations
                                    .causes
                                    .iter()
                                    .any(|explanation| explanation.id == *cause)
                            })
                    {
                        return Err(unsupported(
                            "specialization budget invocation lacks its complete registered coverage proof",
                        ));
                    }
                    selected.budget_proofs.push(proof.clone());
                }
                InvocationWitnessKind::Handler(index) => {
                    let original = facts.handlers.get(*index).ok_or_else(|| {
                        unsupported("effect specialization handler witness is missing")
                    })?;
                    if original.callable_owner != owner {
                        return Err(unsupported(
                            "effect specialization handler belongs to another lexical owner",
                        ));
                    }
                    let source = original.site.ok_or_else(|| {
                        unsupported("effect specialization handler has no canonical lexical site")
                    })?;
                    let target = instance
                        .record
                        .handlers
                        .iter()
                        .find(|mapping| mapping.source == source)
                        .ok_or_else(|| {
                            unsupported("effect specialization handler has no unique remapped site")
                        })?
                        .target;
                    let mut handler = original.clone();
                    handler.site = Some(target);
                    selected.handlers.push(handler);
                }
                InvocationWitnessKind::RetainedHandler(proof) => {
                    selected.retained_handlers.push(proof.clone())
                }
            }
        }
        Ok(selected)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CallableShape {
    Named(DefinitionId),
    Builtin(String),
    Constructor(String),
    Closure(ril_compiler_core::ids::ClosureSiteId),
    Symbolic(u32, Vec<String>),
}
#[derive(Debug, Clone, PartialEq, Eq)]
struct Shape {
    numeric: BTreeMap<
        crate::sema::numeric_selection::NumericSite,
        (
            crate::numeric_literals::NumberType,
            crate::numeric_literals::EncodedNumber,
        ),
    >,
    expressions: BTreeMap<Site, ExpressionShape>,
    unwraps: BTreeMap<Site, (u32, Vec<String>)>,
    variants: BTreeMap<Site, (String, bool)>,
    budgets: BTreeMap<Site, u64>,
    handlers: BTreeMap<Site, (Option<ril_compiler_core::ids::HandlerSiteId>, Vec<u64>)>,
    keys: Vec<(
        String,
        Site,
        crate::sema::model::Ty,
        crate::sema::model::StaticCoordinate,
    )>,
    recipes: Vec<(
        CallableShape,
        Vec<ril_compiler_core::ids::HandlerSiteId>,
        crate::sema::model::Ty,
    )>,
}
type ExpressionShape = (
    crate::sema::model::Ty,
    Vec<CallableShape>,
    Option<Vec<(Option<String>, bool)>>,
);
fn callable_shape(
    facts: &SemanticFacts,
    callable: &Callable,
) -> Result<CallableShape, NotImplemented> {
    Ok(match callable {
        Callable::Named(id) => CallableShape::Named(facts.functions[*id].definition),
        Callable::Builtin(name) => CallableShape::Builtin(name.clone()),
        Callable::Constructor(name) => CallableShape::Constructor(name.clone()),
        Callable::Closure(id) => {
            CallableShape::Closure(facts.closures[*id].site.ok_or_else(|| {
                unsupported("effect specialization closure has no lexical identity")
            })?)
        }
        Callable::Symbolic(id, path) => CallableShape::Symbolic(*id, path.clone()),
    })
}
fn shape(facts: &SemanticFacts, original: &SemanticFacts) -> Result<Shape, NotImplemented> {
    let mut numeric = BTreeMap::new();
    for selection in &facts.numeric_selections {
        let current = (selection.ty, selection.encoded.clone());
        if numeric
            .insert(selection.site, current.clone())
            .is_some_and(|previous| previous != current)
        {
            return Err(unsupported(
                "one actual invocation has conflicting numeric receipts for an original site",
            ));
        }
    }
    let mut expressions = BTreeMap::new();
    for fact in &facts.expressions {
        let callables = fact
            .value
            .callables
            .iter()
            .map(|callable| callable_shape(facts, callable))
            .collect::<Result<_, NotImplemented>>()?;
        let signature = fact.value.signature.as_ref().map(|parameters| {
            parameters
                .iter()
                .map(|parameter| {
                    (
                        if let ast::PatternKind::Name(name) = &parameter.pattern.kind {
                            Some(name.clone())
                        } else {
                            None
                        },
                        parameter.default.is_some(),
                    )
                })
                .collect()
        });
        let current = (
            super::numeric::resolved_type(original, &fact.value.ty)?,
            callables,
            signature,
        );
        if expressions
            .insert(site(fact.span), current.clone())
            .is_some_and(|old| old != current)
        {
            return Err(unsupported(
                "one effect invocation has conflicting expression lowering witnesses",
            ));
        }
    }
    Ok(Shape {
        numeric,
        expressions,
        unwraps: facts
            .implicit_unwraps
            .iter()
            .map(|(site, proof)| (*site, (proof.depth, proof.tags.clone())))
            .collect(),
        variants: facts
            .variant_projections
            .iter()
            .map(|(site, proof)| (*site, (proof.tag.clone(), proof.direct)))
            .collect(),
        budgets: facts
            .budget_proofs
            .iter()
            .map(|proof| (site(proof.span), proof.exhaustion_operation))
            .collect(),
        handlers: facts
            .handlers
            .iter()
            .map(|handler| {
                (
                    site(handler.span),
                    (handler.site, handler.operations.clone()),
                )
            })
            .collect(),
        keys: facts
            .static_key_checks
            .iter()
            .map(|check| {
                (
                    check.binder.clone(),
                    site(check.argument),
                    check.receiver.clone(),
                    check.coordinate.clone(),
                )
            })
            .collect(),
        recipes:facts.retained_handlers.iter().map(|proof|Ok((callable_shape(original,&proof.callable)?,proof.handlers.iter().map(|id|original.handlers.get(*id).and_then(|handler|handler.site).ok_or_else(||unsupported("retained specialization proof references an unowned handler"))).collect::<Result<_,_>>()?,proof.answer.clone()))).collect::<Result<_,NotImplemented>>()?,
    })
}

pub(super) fn builtins(facts: &SemanticFacts) -> Result<BTreeMap<Site, String>, NotImplemented> {
    let mut observations = BTreeMap::<Site, Option<String>>::new();
    for fact in &facts.expressions {
        let current = if let [Callable::Builtin(name)] = fact.value.callables.as_slice()
            && (name.starts_with("Num::__convert_")
                || name.starts_with("Deque::__new_")
                || name.starts_with("Heap::__new_")
                || name.starts_with("Channel::__bounded_")
                || matches!(name.as_str(), "Concurrent::fork" | "Concurrent::join"))
        {
            Some(name.clone())
        } else {
            None
        };
        observations
            .entry(site(fact.span))
            .and_modify(|previous| {
                if *previous != current {
                    *previous = None;
                }
            })
            .or_insert(current);
    }
    Ok(observations
        .into_iter()
        .filter_map(|(site, name)| name.map(|name| (site, name)))
        .collect())
}
