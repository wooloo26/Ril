//! Evidence for actual continuation-answer handoffs. A frozen graph records an
//! observation; it does not imply copying, freshness, or additional permission.
use super::{
    copy_contract::CopyValueSnapshot,
    effect_identity::InvocationContext,
    facts::{LoanId, ScopeId},
};
use ril_compiler_core::{diagnostic::CauseId, source::Span};
use ril_syntax::ast::ParameterMode;

#[derive(Debug, Clone)]
pub struct OperationLoanStart {
    pub loan: LoanId,
    pub activation: ScopeId,
    pub boundary: u32,
    pub handler: usize,
    pub operation: u64,
    pub parameter: u32,
    pub temporary: bool,
    pub context: InvocationContext,
    pub source: CopyValueSnapshot,
    pub allocation_epoch: usize,
    pub span: Span,
    pub cause: CauseId,
}

#[derive(Debug, Clone)]
pub struct OperationReception {
    pub parameter: u32,
    pub mode: ParameterMode,
    pub loan: Option<LoanId>,
}

#[derive(Debug, Clone)]
pub struct ScopeBindingObservation {
    pub binding: usize,
    pub value: super::model::Value,
    pub cell: Option<super::facts::NodeId>,
    pub forwarded: std::collections::BTreeSet<usize>,
    pub alive: bool,
}

#[derive(Debug, Clone)]
pub struct ContinuationScopeExit {
    pub activation: ScopeId,
    pub boundary: u32,
    pub epoch: usize,
    pub binding_frontier: usize,
    pub retired_bindings: std::collections::BTreeSet<usize>,
    pub protected_bindings: std::collections::BTreeSet<usize>,
    pub alive_bindings: std::collections::BTreeSet<usize>,
    pub bindings: Vec<ScopeBindingObservation>,
    /// Linear protection-root observations; no unrelated pairwise relations.
    pub nodes: Vec<super::copy_contract::CopyNode>,
    pub answer_before: CopyValueSnapshot,
    pub answer_received: CopyValueSnapshot,
}

use super::{
    SemanticFacts,
    copy_contract::CopyInvocationStatus,
    facts::{NodeId, Participant},
    model::{AnswerTransport, Ty, Value},
};
use std::collections::{BTreeMap, BTreeSet};

type Failure = (Span, Option<CauseId>, String);

fn fail(span: Span, cause: CauseId, message: &str) -> Failure {
    (span, Some(cause), message.into())
}

fn nested(value: &Value) -> impl Iterator<Item = &Value> {
    [
        &value.option_payload,
        &value.result_payload,
        &value.result_success,
        &value.result_error,
        &value.variant_payload,
    ]
    .into_iter()
    .flatten()
    .map(Box::as_ref)
    .chain(value.variant_witnesses.values().map(Box::as_ref))
}

fn transported(value: &Value, moves: &[(NodeId, NodeId)]) -> Value {
    fn remap(value: &mut Value, recent: NodeId, older: NodeId) {
        value.origins.remap(recent, older);
        for payload in [
            &mut value.option_payload,
            &mut value.result_payload,
            &mut value.result_success,
            &mut value.result_error,
            &mut value.variant_payload,
        ]
        .into_iter()
        .flatten()
        .chain(value.variant_witnesses.values_mut())
        {
            remap(payload, recent, older);
        }
    }
    let mut result = value.clone();
    for &(recent, older) in moves {
        remap(&mut result, recent, older);
    }
    result
}

fn context_valid(context: InvocationContext, facts: &SemanticFacts) -> bool {
    context.invocation.is_none_or(|id| {
        facts
            .copy_invocations
            .get(id.0 as usize)
            .is_some_and(|call| call.id == id && call.status == CopyInvocationStatus::Completed)
    }) && context.closure_invocation.is_none_or(|id| {
        facts
            .closure_invocations
            .get(id.0 as usize)
            .is_some_and(|call| {
                call.id == id
                    && Some(call.closure) == context.closure
                    && call.status == CopyInvocationStatus::Completed
            })
    }) && context.default_use.is_none_or(|id| {
        facts
            .default_uses
            .get(id.0 as usize)
            .is_some_and(|use_| use_.id == id)
    })
}

fn snapshot_valid(snapshot: &CopyValueSnapshot, facts: &SemanticFacts) -> bool {
    let nodes: BTreeMap<_, _> = snapshot
        .nodes
        .iter()
        .map(|node| (node.origin, node))
        .collect();
    if nodes.len() != snapshot.nodes.len() {
        return false;
    }
    let mut visited = BTreeSet::new();
    let mut pending = vec![&snapshot.value];
    while let Some(value) = pending.pop() {
        if value.cause.0 as usize >= facts.explanations.causes.len() {
            return false;
        }
        pending.extend(nested(value));
        for origin in &value.origins.nodes {
            if visited.insert(*origin) {
                let Some(node) = nodes.get(origin) else {
                    return false;
                };
                if origin.0 as usize >= facts.heap.nodes.len() {
                    return false;
                }
                let fields: BTreeMap<_, _> = node
                    .fields
                    .iter()
                    .map(|(slot, value)| (slot.clone(), value.origins.nodes.clone()))
                    .collect();
                if fields.len() != node.fields.len() || fields != node.fact.fields {
                    return false;
                }
                pending.extend(node.fields.iter().map(|(_, value)| value));
            }
        }
    }
    if visited.len() != nodes.len() {
        return false;
    }
    let mut relations = BTreeSet::new();
    for (a, b, relation) in &snapshot.relations {
        if !nodes.contains_key(a)
            || !nodes.contains_key(b)
            || !relations.insert((*a, *b))
            || relation.equal == super::relations::Condition::TRUE
                && relation.disjoint == super::relations::Condition::TRUE
        {
            return false;
        }
    }
    nodes.keys().enumerate().all(|(index, a)| {
        nodes
            .keys()
            .skip(index)
            .all(|b| relations.contains(&(*a, *b)))
    }) && relations.len() == nodes.len().saturating_mul(nodes.len() + 1) / 2
}

fn ordinary_snapshot(
    snapshot: &CopyValueSnapshot,
    facts: &SemanticFacts,
    ended: &BTreeSet<LoanId>,
) -> bool {
    let mut pending = vec![&snapshot.value];
    pending.extend(
        snapshot
            .nodes
            .iter()
            .flat_map(|node| node.fields.iter().map(|(_, value)| value)),
    );
    while let Some(value) = pending.pop() {
        if !value.results.is_empty()
            || !value.outer_results.is_empty()
            || !value.scoped.is_empty()
            || !value.callables.is_empty()
            || !value.pending_copies.is_empty()
            || value.mutable_environment
            || value.observer_environment
            || !ordinary_answer_type(&value.ty, facts)
            || value.participants.iter().any(
                |participant| matches!(participant,Participant::Loan(loan) if ended.contains(loan)),
            )
        {
            return false;
        }
        pending.extend(nested(value));
    }
    true
}

fn ordinary_answer_type(ty: &Ty, facts: &SemanticFacts) -> bool {
    use super::model::TypeArgument;
    use ril_syntax::ast::{TypeExpr, TypeKind};
    fn syntax(
        source: &TypeExpr,
        env: &BTreeMap<String, TypeArgument>,
        budget: &mut usize,
    ) -> Option<Ty> {
        *budget = budget.checked_sub(1)?;
        Some(match &source.kind {
            TypeKind::Name { path, arguments } => {
                let name = path.join("::");
                if let Some(argument) = env.get(&name) {
                    match argument {
                        TypeArgument::Type(ty) | TypeArgument::CanonicalType { ty, .. } => {
                            return Some(*ty.clone());
                        }
                        _ => return None,
                    }
                }
                let mut args = Vec::new();
                for argument in arguments {
                    if let TypeKind::Name { path, arguments } = &argument.kind
                        && arguments.is_empty()
                        && let Some(actual) = env.get(&path.join("::"))
                    {
                        args.push(actual.clone());
                    } else {
                        args.push(TypeArgument::Type(Box::new(syntax(argument, env, budget)?)));
                    }
                }
                match (name.as_str(), args.as_slice()) {
                    ("bool", []) => Ty::Bool,
                    ("str", []) => Ty::Str,
                    ("bytes", []) => Ty::Bytes,
                    (
                        "int" | "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64"
                        | "bigint",
                        [],
                    ) => Ty::Int(name),
                    ("float" | "f32" | "f64", []) => Ty::Float(name),
                    ("Immut", [TypeArgument::Type(inner)]) => Ty::Immutable(inner.clone()),
                    ("Result", [TypeArgument::Type(a), TypeArgument::Type(b)]) => {
                        Ty::Result(a.clone(), b.clone())
                    }
                    (_, []) => Ty::Named(name),
                    _ => Ty::Applied {
                        constructor: name,
                        arguments: args,
                    },
                }
            }
            TypeKind::Optional(inner) => Ty::Optional(Box::new(syntax(inner, env, budget)?)),
            TypeKind::Array { element, .. } => Ty::Array(Box::new(syntax(element, env, budget)?)),
            TypeKind::Tuple(items) => Ty::Tuple(
                items
                    .iter()
                    .map(|item| syntax(item, env, budget))
                    .collect::<Option<_>>()?,
            ),
            TypeKind::Record { fields, row: None } => Ty::Record(
                fields
                    .iter()
                    .map(|field| {
                        Some((
                            field.name.clone(),
                            (field.mutable, syntax(&field.ty, env, budget)?),
                        ))
                    })
                    .collect::<Option<_>>()?,
            ),
            TypeKind::Map { key, value } => Ty::Map(
                Box::new(syntax(key, env, budget)?),
                Box::new(syntax(value, env, budget)?),
            ),
            _ => return None,
        })
    }
    fn visit(
        ty: &Ty,
        facts: &SemanticFacts,
        budget: &mut usize,
        active: &mut BTreeSet<String>,
        productive: bool,
    ) -> bool {
        let Some(next) = budget.checked_sub(1) else {
            return false;
        };
        *budget = next;
        if facts.external_resource_types.contains(ty) {
            return false;
        }
        match ty {
            Ty::Unknown
            | Ty::Never
            | Ty::NumericHole(_)
            | Ty::Generic(_)
            | Ty::Projection { .. }
            | Ty::OpenRecord { .. }
            | Ty::Result(..)
            | Ty::Callable(..) => false,
            Ty::Immutable(inner)
            | Ty::Optional(inner)
            | Ty::Array(inner)
            | Ty::Set(inner)
            | Ty::Range(inner) => visit(inner, facts, budget, active, true),
            Ty::Map(a, b) => {
                visit(a, facts, budget, active, true) && visit(b, facts, budget, active, true)
            }
            Ty::Tuple(items) => items
                .iter()
                .all(|ty| visit(ty, facts, budget, active, true)),
            Ty::Record(fields) => fields
                .values()
                .all(|(_, ty)| visit(ty, facts, budget, active, true)),
            Ty::Named(name)
            | Ty::Applied {
                constructor: name, ..
            } if !ty.scalar() => {
                let Some(declaration) = facts.external_type_declarations.get(name) else {
                    return false;
                };
                if declaration.opaque || active.len() >= 128 {
                    return false;
                }
                let key = format!("{ty:?}");
                if active.contains(&key) {
                    return productive;
                }
                let arguments = match ty {
                    Ty::Applied { arguments, .. } => arguments.as_slice(),
                    _ => &[],
                };
                if arguments.len() != declaration.generics.len() {
                    return false;
                }
                let env: BTreeMap<_, _> = declaration
                    .generics
                    .iter()
                    .zip(arguments)
                    .map(|(parameter, argument)| (parameter.name.clone(), argument.clone()))
                    .collect();
                let Some(expanded) = declaration
                    .value
                    .as_ref()
                    .and_then(|value| syntax(value, &env, budget))
                else {
                    return false;
                };
                if expanded == *ty {
                    return false;
                }
                active.insert(key.clone());
                let ordinary = visit(&expanded, facts, budget, active, productive);
                active.remove(&key);
                ordinary
            }
            _ => ty.scalar(),
        }
    }
    visit(ty, facts, &mut 4096, &mut BTreeSet::new(), false)
}

fn same_snapshot_graph(a: &CopyValueSnapshot, b: &CopyValueSnapshot) -> bool {
    a.nodes.len() == b.nodes.len()
        && a.nodes.iter().zip(&b.nodes).all(|(a, b)| {
            a.origin == b.origin
                && a.fact == b.fact
                && a.fields == b.fields
                && a.length == b.length
                && a.fixed == b.fixed
        })
        && a.relations == b.relations
}

fn scope_protection(
    exit: &ContinuationScopeExit,
    step: &super::ResumptionStep,
    facts: &SemanticFacts,
) -> Option<BTreeSet<usize>> {
    let observations: BTreeMap<_, _> = exit
        .bindings
        .iter()
        .map(|binding| (binding.binding, binding))
        .collect();
    let nodes: BTreeMap<_, _> = exit.nodes.iter().map(|node| (node.origin, node)).collect();
    if observations.len() != exit.bindings.len() || nodes.len() != exit.nodes.len() {
        return None;
    }
    let mut protected = BTreeSet::new();
    protected.extend(
        facts
            .handlers
            .iter()
            .flat_map(|handler| handler.lexical.values().copied())
            .filter(|id| *id < exit.binding_frontier),
    );
    protected.extend(
        facts
            .closures
            .iter()
            .flat_map(|closure| closure.captures.iter().copied())
            .filter(|id| *id < exit.binding_frontier),
    );
    protected.extend(
        facts
            .functions
            .iter()
            .flat_map(|function| function.captures.iter().copied())
            .filter(|id| *id < exit.binding_frontier),
    );
    protected.extend(
        facts
            .functions
            .iter()
            .filter(|function| function.owner.is_some())
            .flat_map(|function| function.lexical.values().copied())
            .filter(|id| *id < exit.binding_frontier),
    );
    let arms: BTreeSet<_> = facts
        .resumption_steps
        .iter()
        .filter(|other| {
            other.boundary == step.boundary
                && facts.scope_parents.get(&other.owner) == Some(&exit.activation)
        })
        .map(|other| other.owner)
        .chain([step.owner])
        .collect();
    protected.extend(
        facts
            .bindings
            .iter()
            .enumerate()
            .filter_map(|(id, binding)| {
                (id < exit.binding_frontier && arms.contains(&binding.owner)).then_some(id)
            }),
    );
    let mut bindings = BTreeSet::new();
    let mut seen_nodes = BTreeSet::new();
    let mut seen_participants = BTreeSet::new();
    let mut participants = BTreeSet::new();
    let mut values = Vec::new();
    loop {
        let prior = (protected.len(), seen_nodes.len(), participants.len());
        let pending: Vec<_> = protected
            .iter()
            .copied()
            .filter(|id| !bindings.contains(id))
            .collect();
        for id in pending {
            let observation = observations.get(&id)?;
            bindings.insert(id);
            protected.extend(&observation.forwarded);
            values.push(&observation.value);
            if let Some(cell) = observation.cell
                && seen_nodes.insert(cell)
            {
                values.extend(nodes.get(&cell)?.fields.iter().map(|(_, value)| value));
            }
        }
        while let Some(value) = values.pop() {
            protected.extend(&value.sources);
            protected.extend(&value.scoped);
            protected.extend(&value.callback_parameters);
            participants.extend(&value.participants);
            for bound in &value.callable_bounds {
                protected.extend(bound.lexical.values().copied());
            }
            let mut returns: Vec<_> = value
                .callable_returns
                .iter()
                .map(|bound| bound.as_ref())
                .collect();
            while let Some(bound) = returns.pop() {
                protected.extend(bound.lexical.values().copied());
                returns.extend(bound.predecessors.iter().map(|bound| bound.as_ref()));
            }
            values.extend(nested(value));
            for origin in &value.origins.nodes {
                if seen_nodes.insert(*origin) {
                    values.extend(nodes.get(origin)?.fields.iter().map(|(_, value)| value));
                }
            }
        }
        for participant in participants.clone() {
            if !seen_participants.insert(participant) {
                continue;
            }
            match participant {
                Participant::Root(root) => {
                    protected.insert(root.0 as usize);
                }
                Participant::Loan(loan) => participants.extend(facts.loan_parents.get(&loan)?),
            }
        }
        if prior == (protected.len(), seen_nodes.len(), participants.len()) && values.is_empty() {
            break;
        }
    }
    if seen_nodes.len() != nodes.len() {
        return None;
    }
    for node in nodes.values() {
        if node.origin.0 as usize >= facts.heap.nodes.len()
            || node
                .fields
                .iter()
                .map(|(slot, value)| (slot.clone(), value.origins.nodes.clone()))
                .collect::<BTreeMap<_, _>>()
                != node.fact.fields
        {
            return None;
        }
    }
    Some(protected)
}

fn requires_scope_exit(step: &super::ResumptionStep, facts: &SemanticFacts) -> bool {
    let value = &step.continuation_value.value;
    if value.permission != super::facts::Permission::Write || !value.construction {
        return false;
    }
    let Some(activation) = facts.scope_parents.get(&step.owner) else {
        return false;
    };
    value
        .sources
        .iter()
        .copied()
        .chain(
            value
                .participants
                .iter()
                .filter_map(|participant| match participant {
                    Participant::Root(root) => Some(root.0 as usize),
                    _ => None,
                }),
        )
        .any(|id| {
            facts.bindings.get(id).is_some_and(|binding| {
                binding.owner == *activation
                    && binding.lexical_scope == step.boundary
                    && !binding.parameter
                    && binding.mode.is_mutable()
                    && !binding.value.construction
            })
        })
}

fn validate_scope_exit(
    exit: &ContinuationScopeExit,
    step: &super::ResumptionStep,
    facts: &SemanticFacts,
) -> Result<(), Failure> {
    use super::facts::{OriginKind, Permission, Publication};
    use ril_syntax::ast::{BindingMode, ExprKind, PatternKind, StmtKind};
    let bad = |message| fail(step.span, step.cause, message);
    if exit.boundary != step.boundary
        || facts.scope_parents.get(&step.owner) != Some(&exit.activation)
        || exit.epoch != step.continuation_epoch
        || exit.binding_frontier > facts.bindings.len()
        || exit.retired_bindings.is_empty()
        || !snapshot_valid(&exit.answer_before, facts)
        || !snapshot_valid(&exit.answer_received, facts)
        || exit.answer_received.value != step.continuation_value.value
        || !same_snapshot_graph(&exit.answer_before, &exit.answer_received)
        || !same_snapshot_graph(&exit.answer_received, &step.continuation_value)
    {
        return Err(bad(
            "continuation scope exit lacks this boundary's unchanged answer graph and epoch",
        ));
    }
    // A named answer binder is the first binding created after this receipt.
    // Its actual ID prevents lowering the observation frontier to hide roots.
    if let Some(arm)=facts.handlers.get(step.handler).and_then(|handler|handler.arms.iter().find(|arm|{
        let ExprKind::Block(block)=&arm.body.kind else{return false;};
        block.statements.iter().any(|statement|matches!(&statement.kind,StmtKind::Binding(binding) if binding.value.span==step.span))
    })) && let ExprKind::Block(block)=&arm.body.kind
        && let Some(binding)=block.statements.iter().find_map(|statement|match &statement.kind {
            StmtKind::Binding(binding) if binding.value.span==step.span=>Some(binding),_=>None,
        }) && let PatternKind::Name(name)=&binding.pattern.kind {
        let actual=facts.bindings.iter().enumerate().find(|(_,actual)|actual.owner==step.owner&&!actual.parameter&&actual.span==binding.pattern.span&&actual.name==*name);
        if actual.is_none_or(|(id,_)|id!=exit.binding_frontier) {return Err(bad("scope-exit observation frontier differs from its actual answer reception"));}
    }
    let observations: BTreeMap<_, _> = exit
        .bindings
        .iter()
        .map(|observation| (observation.binding, observation))
        .collect();
    if observations.len() != exit.bindings.len()
        || exit.bindings.iter().any(|observation| {
            observation.binding >= exit.binding_frontier
                || !facts
                    .bindings
                    .get(observation.binding)
                    .is_some_and(|binding| binding.root.0 as usize == observation.binding)
        })
        || exit
            .bindings
            .iter()
            .filter_map(|observation| observation.alive.then_some(observation.binding))
            .collect::<BTreeSet<_>>()
            != exit.alive_bindings
    {
        return Err(bad(
            "scope exit lacks its historical binding authority observations",
        ));
    }
    let protected = scope_protection(exit, step, facts)
        .ok_or_else(|| bad("scope-exit protection roots have incomplete epoch observations"))?;
    if protected != exit.protected_bindings {
        return Err(bad(
            "scope-exit protection set differs from independently closed handler and capture roots",
        ));
    }
    let roots: BTreeSet<_> = exit
        .answer_before
        .nodes
        .iter()
        .flat_map(|node| node.fact.writable_roots.iter().map(|root| root.0 as usize))
        .collect();
    for id in &exit.retired_bindings {
        let binding = facts
            .bindings
            .get(*id)
            .ok_or_else(|| bad("scope exit retires an unknown binding"))?;
        if binding.owner != exit.activation
            || binding.lexical_scope != exit.boundary
            || binding.parameter
            || matches!(binding.mode, BindingMode::Scoped | BindingMode::ScopedMut)
            || protected.contains(id)
            || !roots.contains(id)
            || !exit.alive_bindings.contains(id)
        {
            return Err(bad(
                "scope exit cannot retire a parameter, capture, ambient or unrelated writer",
            ));
        }
        let observation = observations
            .get(id)
            .ok_or_else(|| bad("retired binding lacks an epoch observation"))?;
        let value = CopyValueSnapshot {
            value: observation.value.clone(),
            nodes: Vec::new(),
            relations: Vec::new(),
        };
        if !ordinary_snapshot(&value, facts, &BTreeSet::new()) {
            return Err(bad(
                "scope exit cannot retire resource, Result, scoped or unresolved storage",
            ));
        }
    }
    for id in &roots {
        let observation = observations
            .get(id)
            .ok_or_else(|| bad("answer writer lacks an epoch observation"))?;
        let binding = &facts.bindings[*id];
        let mut parent = Some(exit.activation);
        let mut ancestor = false;
        let mut visited = BTreeSet::new();
        while let Some(scope) = parent {
            if !visited.insert(scope) {
                break;
            }
            if scope == binding.owner {
                ancestor = true;
                break;
            }
            parent = facts.scope_parents.get(&scope).copied();
        }
        if !observation.alive
            && (binding.parameter && ancestor
                || binding.owner == exit.activation && binding.lexical_scope == exit.boundary
                || binding.owner == ScopeId(0) && binding.alive)
        {
            return Err(bad(
                "scope exit cannot mark an active parent, ambient or current-boundary writer historically dead",
            ));
        }
    }
    let mut received = exit.answer_received.value.clone();
    received.construction = exit.answer_before.value.construction;
    received.publication = exit.answer_before.value.publication;
    if received != exit.answer_before.value {
        return Err(bad(
            "scope exit changed permissions, origins, participants or other answer evidence",
        ));
    }
    if exit.answer_received.value != exit.answer_before.value {
        if exit.answer_before.value.permission != Permission::Write
            || exit.answer_before.value.publication == Publication::Immutable
            || !exit.answer_received.value.construction
            || exit.answer_received.value.publication != Publication::Unpublished
        {
            return Err(bad(
                "scope exit cannot restore construction through a read-only or immutable path",
            ));
        }
        let nodes: BTreeMap<_, _> = exit
            .answer_before
            .nodes
            .iter()
            .map(|node| (node.origin, node))
            .collect();
        let mut writable = exit.answer_before.value.origins.nodes.clone();
        let mut seen = BTreeSet::new();
        loop {
            let pending: Vec<_> = writable
                .iter()
                .copied()
                .filter(|node| !seen.contains(node))
                .collect();
            if pending.is_empty() {
                break;
            }
            for origin in pending {
                seen.insert(origin);
                let node = nodes
                    .get(&origin)
                    .ok_or_else(|| bad("scope exit omitted a writable origin"))?;
                if !matches!(node.fact.kind, OriginKind::Fresh(_) | OriginKind::Older(_)) {
                    return Err(bad(
                        "scope exit cannot grant fresh construction to external storage",
                    ));
                }
                for (_, value) in &node.fields {
                    if value.permission == Permission::Write {
                        writable.extend(&value.origins.nodes);
                    }
                }
            }
        }
        if roots.iter().any(|id| {
            observations
                .get(id)
                .is_none_or(|observation| observation.alive && !exit.retired_bindings.contains(id))
        }) {
            return Err(bad(
                "scope exit retains an external writer to the answer graph",
            ));
        }
    }
    Ok(())
}

/// Check actual identities and complete frozen material independently of the
/// checker that executed the suffix. This is not a replacement permission rule.
pub fn validate(facts: &SemanticFacts) -> Result<(), Failure> {
    // A missing table is not evidence that no non-tail resumption occurred.
    // Reconstruct required input-expression events from the resolved arm ASTs;
    // their exact event indices and dynamic contexts still identify each use.
    let mut suffix_sites = BTreeSet::new();
    for handler in &facts.handlers {
        for arm in &handler.arms {
            use ril_syntax::ast::{ControlOperation, ExprKind, StmtKind};
            let ExprKind::Block(block) = &arm.body.kind else {
                continue;
            };
            if let Some((index, span)) =
                block
                    .statements
                    .iter()
                    .enumerate()
                    .find_map(|(index, statement)| {
                        let expression = match &statement.kind {
                            StmtKind::Expr { expression, .. } => expression,
                            StmtKind::Binding(binding) => &binding.value,
                            _ => return None,
                        };
                        matches!(
                            expression.kind,
                            ExprKind::Control {
                                operation: ControlOperation::Resume,
                                ..
                            }
                        )
                        .then_some((index, expression.span))
                    })
                && !(index + 1 == block.statements.len()
                    && matches!(block.statements[index].kind, StmtKind::Expr { .. }))
            {
                suffix_sites.insert((span.file.0, span.start, span.end));
            }
        }
    }
    for event in &facts.invocation_expressions {
        let Some(expression) = facts.expressions.get(event.expression) else {
            continue;
        };
        if suffix_sites.contains(&(
            expression.span.file.0,
            expression.span.start,
            expression.span.end,
        )) && facts
            .resumption_steps
            .iter()
            .filter(|step| {
                step.continuation_expression == event.expression && step.context == event.context
            })
            .count()
            != 1
        {
            return Err(fail(
                expression.span,
                expression.value.cause,
                "actual non-tail continuation expression has no unique resumption step",
            ));
        }
    }
    let mut starts = BTreeMap::new();
    for start in &facts.operation_loan_starts {
        let mode = facts
            .operations
            .values()
            .find(|operation| operation.identity == start.operation)
            .and_then(|operation| operation.parameters.get(start.parameter as usize))
            .map(|(mode, _)| *mode);
        if starts.insert(start.loan, start).is_some()
            || facts.loan_parents.get(&start.loan) != Some(&start.source.value.participants)
            || !facts.allocated_scopes.contains(&start.activation)
            || start.allocation_epoch > facts.allocation_history.len()
            || mode
                != Some(if start.temporary {
                    ParameterMode::Mut
                } else {
                    ParameterMode::SharedMut
                })
            || facts
                .handlers
                .get(start.handler)
                .is_none_or(|handler| !handler.operations.contains(&start.operation))
            || !context_valid(start.context, facts)
            || !snapshot_valid(&start.source, facts)
        {
            return Err(fail(
                start.span,
                start.cause,
                "operation loan entry lacks its actual source, mode or activation",
            ));
        }
    }
    for step in &facts.resumption_steps {
        let bad = |message| fail(step.span, step.cause, message);
        let operation = facts
            .operations
            .values()
            .find(|operation| operation.identity == step.operation)
            .ok_or_else(|| bad("resumption has no resolved operation"))?;
        if let Some(exit) = &step.scope_exit {
            validate_scope_exit(exit, step, facts)?;
        } else if requires_scope_exit(step, facts) {
            return Err(bad(
                "fresh reception of a continuation-local writer lacks its scope-exit proof",
            ));
        }
        if !facts.allocated_scopes.contains(&step.owner)
            || !context_valid(step.context, facts)
            || facts
                .handlers
                .get(step.handler)
                .is_none_or(|handler| !handler.operations.contains(&step.operation))
            || step.continuation_epoch > step.completion_epoch
            || step.completion_epoch > facts.allocation_history.len()
            || step.continuation_value.value.cause != step.continuation
            || step.arm_value.value.cause != step.cause
            || step.continuation_value.value.ty != step.body_answer
            || step.arm_value.value.ty != step.arm_answer
            || !snapshot_valid(&step.continuation_value, facts)
            || !snapshot_valid(&step.arm_value, facts)
            || step.operation_receptions.len() != operation.parameters.len()
        {
            return Err(bad(
                "resumption answer lacks a complete actual snapshot, epoch or reception",
            ));
        }
        let expression = facts
            .expressions
            .get(step.continuation_expression)
            .ok_or_else(|| bad("resumption continuation expression is missing"))?;
        if expression.span != step.span
            || expression.value
                != transported(
                    &step.continuation_value.value,
                    &facts.allocation_history[step.continuation_epoch..],
                )
            || !facts.invocation_expressions.iter().any(|event| {
                event.expression == step.continuation_expression && event.context == step.context
            })
        {
            return Err(bad(
                "resumption answer borrows a different expression or invocation",
            ));
        }
        let output = facts
            .expressions
            .get(step.arm_expression)
            .ok_or_else(|| bad("resumption suffix expression is missing"))?;
        if output.value
            != transported(
                &step.arm_value.value,
                &facts.allocation_history[step.completion_epoch..],
            )
            || !facts.invocation_expressions.iter().any(|event| {
                event.expression == step.arm_expression && event.context == step.context
            })
        {
            return Err(bad(
                "resumption suffix graph borrows a different expression or invocation",
            ));
        }
        let mut expected = BTreeSet::new();
        for (index, (receipt, (mode, _))) in step
            .operation_receptions
            .iter()
            .zip(&operation.parameters)
            .enumerate()
        {
            if receipt.parameter != index as u32 || receipt.mode != *mode {
                return Err(bad(
                    "operation reception differs from its resolved parameter",
                ));
            }
            match (mode, receipt.loan) {
                (ParameterMode::Read, None) => {}
                (ParameterMode::Mut | ParameterMode::SharedMut, Some(loan)) => {
                    let start = starts
                        .get(&loan)
                        .ok_or_else(|| bad("operation reception has no loan-entry evidence"))?;
                    if start.activation != step.owner
                        || start.handler != step.handler
                        || start.operation != step.operation
                        || start.parameter != receipt.parameter
                        || start.context != step.context
                        || start.boundary != step.boundary
                        || start.allocation_epoch > step.continuation_epoch
                    {
                        return Err(bad(
                            "resumption cannot end a loan from another operation or invocation",
                        ));
                    }
                    if *mode == ParameterMode::Mut {
                        expected.insert(loan);
                        if !facts.operation_loan_ends.contains_key(&loan) {
                            return Err(bad("temporary operation loan has no end evidence"));
                        }
                    }
                }
                _ => {
                    return Err(bad(
                        "operation reception cannot erase or invent a borrowing participant",
                    ));
                }
            }
        }
        if expected != step.ended_operation_loans {
            return Err(bad(
                "resumption ended-loan set differs from its actual temporary receptions",
            ));
        }
        if step.transport == AnswerTransport::OrdinaryChecked
            && (!ordinary_snapshot(&step.continuation_value, facts, &expected)
                || !ordinary_snapshot(&step.arm_value, facts, &expected))
        {
            return Err(bad(
                "ordinary suffix cannot transfer unresolved, resource, Result or ended-loan graph state",
            ));
        }
    }
    for proof in &facts.retained_handler_answers {
        if proof.transport != AnswerTransport::OrdinaryChecked {
            continue;
        }
        let bad = |message| fail(proof.span, proof.cause, message);
        if proof.resumption_steps.is_empty() || !facts.allocated_scopes.contains(&proof.activation)
        {
            return Err(bad(
                "ordinary retained answer has no actual resumption steps",
            ));
        }
        let mut seen = BTreeSet::new();
        for index in &proof.resumption_steps {
            let step = facts
                .resumption_steps
                .get(*index)
                .ok_or_else(|| bad("ordinary answer references a missing resumption step"))?;
            if !seen.insert(*index)
                || step.transport != AnswerTransport::OrdinaryChecked
                || step.handler != proof.handler
                || step.operation != proof.operation
                || facts.scope_parents.get(&step.owner) != Some(&proof.activation)
                || step.arm_answer != proof.invocation
                || !ordinary_snapshot(&step.continuation_value, facts, &step.ended_operation_loans)
                || !ordinary_snapshot(&step.arm_value, facts, &step.ended_operation_loans)
            {
                return Err(bad(
                    "ordinary answer lacks this invocation's complete non-resource, non-Result graph",
                ));
            }
        }
    }
    Ok(())
}
