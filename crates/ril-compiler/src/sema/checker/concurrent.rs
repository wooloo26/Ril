//! Structured task and endpoint contracts retain allocation identity across
//! aliases, aggregates and callable environments. They never infer ownership
//! merely from an opaque type spelling.
use super::*;
mod descriptors;
mod message_presence;
pub(super) mod messages;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct DescriptorContext {
    site: (u32, u32, u32),
    discriminator: u32,
    calls: Vec<DescriptorCall>,
    closures: Vec<DescriptorClosure>,
    recursive: bool,
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct DescriptorCall {
    target: DefinitionId,
    caller: Option<CallableOwner>,
    site: (u32, u32, u32),
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct DescriptorClosure {
    target: ClosureSiteId,
    caller: Option<CallableOwner>,
    site: (u32, u32, u32),
}

#[derive(Clone, Default)]
pub(super) struct State {
    pub(super) message_flow: messages::Flow,
    scopes: Vec<NodeId>,
    suspended_scopes: Vec<Vec<NodeId>>,
    task_context: Vec<NodeId>,
    resources: BTreeMap<NodeId, Resource>,
    resource_alternatives: BTreeMap<NodeId, Vec<Resource>>,
    tasks: BTreeMap<NodeId, Task>,
    invalid: BTreeSet<NodeId>,
    receivers: BTreeMap<NodeId, Value>,
    borrowed: BTreeMap<NodeId, BTreeSet<NodeId>>,
    clone_sources: Vec<BTreeSet<NodeId>>,
    messages: BTreeMap<NodeId, Vec<Value>>,
    uncertain_messages: BTreeSet<NodeId>,
    iteration_bounds: BTreeMap<NodeId, Option<u64>>,
    scope_callbacks: BTreeSet<usize>,
    transport_results: BTreeSet<u32>,
}
impl State {
    pub(super) fn cancellation_retained_values(&self) -> impl Iterator<Item = &Value> {
        self.tasks
            .values()
            .map(|task| &task.output)
            .chain(self.receivers.values())
            .chain(self.messages.values().flatten())
    }
    pub(super) fn cancellation_recency_nodes(&self) -> BTreeSet<NodeId> {
        self.resources
            .keys()
            .flat_map(|node| {
                self.resource_variants(*node)
                    .map(move |resource| (node, resource))
            })
            .flat_map(|(node, resource)| {
                [
                    Some(*node),
                    Some(resource.scope),
                    resource.task,
                    resource.channel,
                ]
                .into_iter()
                .flatten()
            })
            .chain(self.scopes.iter().copied())
            .chain(self.task_context.iter().copied())
            .chain(
                self.borrowed.iter().flat_map(|(source, tasks)| {
                    std::iter::once(*source).chain(tasks.iter().copied())
                }),
            )
            .chain(self.tasks.values().flat_map(|task| {
                task.output
                    .origins
                    .nodes
                    .iter()
                    .copied()
                    .chain(task.borrows.iter().copied())
            }))
            .chain(
                self.receivers
                    .values()
                    .flat_map(|value| value.origins.nodes.iter().copied()),
            )
            .chain(self.messages.iter().flat_map(|(channel, values)| {
                std::iter::once(*channel).chain(
                    values
                        .iter()
                        .flat_map(|value| value.origins.nodes.iter().copied()),
                )
            }))
            .collect()
    }
    fn cancellation_internal(&self, resource: &Resource, before: &State, scope: NodeId) -> bool {
        resource.scope == scope
            || !before.resources.contains_key(&resource.scope)
            || resource
                .task
                .and_then(|task| self.resources.get(&task))
                .is_some_and(|task| {
                    task.scope == scope || !before.resources.contains_key(&task.scope)
                })
    }
    pub(super) fn cancellation_external_compatible(&self, before: &State, scope: NodeId) -> bool {
        for (node, resource) in &before.resources {
            if self.cancellation_internal(resource, before, scope) {
                continue;
            }
            if self.resources.get(node) != Some(resource)
                || self.resource_alternatives.get(node) != before.resource_alternatives.get(node)
                || self.invalid.contains(node) != before.invalid.contains(node)
            {
                return false;
            }
            let external_borrows = |state: &State| {
                state
                    .borrowed
                    .get(node)
                    .into_iter()
                    .flatten()
                    .filter(|task| {
                        state
                            .resources
                            .get(task)
                            .is_none_or(|task| !state.cancellation_internal(task, before, scope))
                    })
                    .copied()
                    .collect::<BTreeSet<_>>()
            };
            if external_borrows(self) != external_borrows(before) {
                return false;
            }
            if let Some(channel) = resource.channel
                && (self.messages.get(&channel) != before.messages.get(&channel)
                    || self.uncertain_messages.contains(&channel)
                        != before.uncertain_messages.contains(&channel))
            {
                return false;
            }
            if let Some(task) = before.tasks.get(node)
                && self.tasks.get(node).is_none_or(|current| {
                    current.output != task.output
                        || current.borrows != task.borrows
                        || ((!task.output.results.is_empty() || !task.borrows.is_empty())
                            && (current.joined != task.joined || current.observed != task.observed))
                })
            {
                return false;
            }
        }
        self.resources
            .iter()
            .filter(|(node, _)| !before.resources.contains_key(node))
            .all(|(node, resource)| {
                if self
                    .resource_alternatives
                    .get(node)
                    .is_some_and(|values| !values.is_empty())
                {
                    return false;
                }
                self.cancellation_internal(resource, before, scope)
                    || resource
                        .task
                        .filter(|task| !before.tasks.contains_key(task))
                        .and_then(|task| self.tasks.get(&task))
                        .is_some_and(|task| {
                            (task.output.ty.scalar() || task.output.ty == Ty::Never)
                                && task.output.results.is_empty()
                                && task.output.scoped.is_empty()
                                && task.borrows.is_empty()
                        })
                    || (resource.kind == Kind::Task
                        && self.tasks.get(node).is_some_and(|task| {
                            (task.output.ty.scalar() || task.output.ty == Ty::Never)
                                && task.output.results.is_empty()
                                && task.output.scoped.is_empty()
                                && task.borrows.is_empty()
                        }))
            })
    }
    pub(super) fn has_retained_authority(&self) -> bool {
        !self.resources.is_empty()
            || !self.tasks.is_empty()
            || !self.borrowed.is_empty()
            || !self.scopes.is_empty()
            || !self.task_context.is_empty()
    }
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Scope,
    Task,
    Sender,
    Receiver,
    Detached,
}
#[derive(Clone, PartialEq, Eq)]
struct Resource {
    cause: CauseId,
    scope: NodeId,
    task: Option<NodeId>,
    kind: Kind,
    channel: Option<NodeId>,
    formal: bool,
}
#[derive(Clone)]
struct Task {
    output: Value,
    may_fail: bool,
    joined: bool,
    observed: bool,
    borrows: BTreeSet<NodeId>,
}

pub(super) fn is_builtin(name: &str) -> bool {
    matches!(
        name,
        "Concurrent::scope"
            | "Concurrent::fork"
            | "Concurrent::join"
            | "Channel::bounded"
            | "Channel::send"
            | "Channel::recv"
            | "Channel::detach"
            | "Channel::attach"
            | "Channel::close"
    ) || name.starts_with("Channel::__bounded_")
}
pub(super) fn builtin_type(name: &str) -> Option<Ty> {
    if name == "Concurrent::PanicInfo" {
        return Some(panic_info_type());
    }
    if name == "Concurrent::DoubleFaultInfo" {
        return Some(Ty::Record(
            [
                (
                    "primary".into(),
                    (false, Ty::Named("Concurrent::UnwindCause".into())),
                ),
                ("cleanup".into(), (false, panic_info_type())),
            ]
            .into(),
        ));
    }
    matches!(
        name,
        "Concurrent::Scope"
            | "Concurrent::TaskFault"
            | "Concurrent::UnwindCause"
            | "Channel::ChannelError"
    )
    .then(|| Ty::Named(name.into()))
}
fn panic_info_type() -> Ty {
    Ty::Record(
        [
            ("message".into(), (false, Ty::Str)),
            (
                "index".into(),
                (false, Ty::Optional(Box::new(Ty::Int("int".into())))),
            ),
        ]
        .into(),
    )
}
fn argument(ty: &Ty, name: &str) -> Option<Ty> {
    match ty {
        Ty::Immutable(inner) => argument(inner, name),
        Ty::Applied {
            constructor,
            arguments,
        } if constructor == name && arguments.len() == 1 => match &arguments[0] {
            TypeArgument::Type(ty) | TypeArgument::CanonicalType { ty, .. } => Some(*ty.clone()),
            _ => None,
        },
        _ => None,
    }
}
impl Checker {
    fn nonfaulting_literal_child(&self, action: &Value) -> bool {
        fn expression(value: &Expr) -> bool {
            match &value.kind {
                ExprKind::Literal(_) => true,
                ExprKind::Block(value) => block(value),
                _ => false,
            }
        }
        fn block(value: &Block) -> bool {
            value.where_items.is_empty() && value.statements.iter().all(|statement| {
                matches!(&statement.kind, StmtKind::Expr { expression: value, .. } if expression(value))
            })
        }
        !action.callables.is_empty()
            && action.callables.iter().all(|callable| match callable {
                Callable::Closure(id) => {
                    self.closures[*id].parameters.is_empty()
                        && !self.has_retained_handlers(callable)
                        && expression(&self.closures[*id].body)
                }
                _ => false,
            })
    }
    pub(super) fn merge_cancellation_external_tasks(
        &mut self,
        prefix: &State,
        before: &State,
        scope: NodeId,
    ) {
        // Tasks allocated in an older scope survive this boundary. A possible
        // earlier join cannot be repeated; observation requires every prefix.
        for (node, resource) in &prefix.resources {
            if resource.kind != Kind::Task || prefix.cancellation_internal(resource, before, scope)
            {
                continue;
            }
            if let Some(task) = prefix.tasks.get(node) {
                self.concurrency
                    .resources
                    .entry(*node)
                    .or_insert_with(|| resource.clone());
                self.concurrency
                    .tasks
                    .entry(*node)
                    .and_modify(|current| {
                        current.joined |= task.joined;
                        current.observed &= task.observed;
                        current.may_fail |= task.may_fail;
                    })
                    .or_insert_with(|| task.clone());
            }
        }
    }
    pub(super) fn concurrent_range_bound(
        &mut self,
        node: NodeId,
        start: Option<&Value>,
        end: Option<&Value>,
        inclusive: bool,
    ) {
        let bounds = start
            .and_then(|value| value.constant.as_ref())
            .zip(end.and_then(|value| value.constant.as_ref()));
        let bound = if let Some((Constant::Integer(start), Constant::Integer(end))) = bounds {
            end.checked_sub(*start)
                .and_then(|length| length.checked_add(i128::from(inclusive)))
                .and_then(|length| u64::try_from(length.max(0)).ok())
        } else {
            None
        };
        self.concurrency.iteration_bounds.insert(node, bound);
    }
    pub(super) fn concurrent_iteration_at_most_once(&self, value: &Value) -> bool {
        match self.expanded(&value.ty, &mut BTreeSet::new()) {
            Ty::Array(_) => self
                .known_array_length(value)
                .is_some_and(|length| length <= 1),
            Ty::Range(_) => {
                !value.origins.nodes.is_empty()
                    && value.origins.nodes.iter().all(|node| {
                        self.concurrency
                            .iteration_bounds
                            .get(node)
                            .is_some_and(|length| length.is_some_and(|length| length <= 1))
                    })
            }
            _ => false,
        }
    }
    pub(super) fn concurrent_iteration_definitely_nonempty(&self, value: &Value) -> bool {
        match self.expanded(&value.ty, &mut BTreeSet::new()) {
            Ty::Array(_) => self
                .known_array_length(value)
                .is_some_and(|length| length > 0),
            Ty::Range(_) => {
                !value.origins.nodes.is_empty()
                    && value.origins.nodes.iter().all(|node| {
                        self.concurrency
                            .iteration_bounds
                            .get(node)
                            .is_some_and(|length| length.is_some_and(|length| length > 0))
                    })
            }
            _ => false,
        }
    }
    fn concurrent_applied(&self, name: &str, inner: Ty) -> Ty {
        let argument = match self.selected_type_key(&inner) {
            Some(key) => TypeArgument::CanonicalType {
                ty: Box::new(inner),
                key,
            },
            None => TypeArgument::Type(Box::new(inner)),
        };
        Ty::Applied {
            constructor: name.into(),
            arguments: vec![argument],
        }
    }
    /// A formal descriptor carries an abstract caller-owned lifetime anchor.
    /// Calls with real values keep their existing allocation identity; this
    /// creates no authority or transferable exception for an arbitrary value.
    pub(super) fn concurrent_formal(
        &mut self,
        value: &mut Value,
        index: u32,
        span: Span,
        seen: &mut BTreeSet<String>,
    ) {
        let kind = if value.ty == Ty::Named("Concurrent::Scope".into()) {
            Kind::Scope
        } else if argument(&value.ty, "Concurrent::Task").is_some() {
            Kind::Task
        } else if argument(&value.ty, "Channel::Sender").is_some() {
            Kind::Sender
        } else if argument(&value.ty, "Channel::Receiver").is_some() {
            Kind::Receiver
        } else if argument(&value.ty, "Channel::Detached").is_some() {
            Kind::Detached
        } else {
            return;
        };
        let Some(node) = value.origins.nodes.first().copied() else {
            return;
        };
        if kind != Kind::Scope {
            value.publication = Publication::Immutable;
        }
        let scope = self.heap.symbolic(
            Pivot(self.heap.nodes.len() as u32),
            ScopeId(u32::MAX),
            value.cause,
        );
        self.concurrency.resources.insert(
            node,
            Resource {
                cause: value.cause,
                scope,
                task: self.concurrency.task_context.last().copied(),
                kind,
                channel: None,
                formal: true,
            },
        );
        if kind == Kind::Task {
            let ty = argument(&value.ty, "Concurrent::Task").unwrap();
            let mut output = self.formal_value(ty, index.wrapping_add(1), span, seen);
            if !self.contains_resource(&output) {
                freeze_formal_value(&mut output);
            }
            self.concurrency.tasks.insert(
                node,
                Task {
                    output,
                    may_fail: true,
                    joined: false,
                    observed: false,
                    borrows: BTreeSet::new(),
                },
            );
        }
    }
    pub(super) fn concurrent_scope_callback(&self, id: usize) -> bool {
        self.concurrency.scope_callbacks.contains(&id)
            || self.immediate_scope_closures.contains(&id)
    }
    pub(super) fn cancellation_task(&self) -> Option<NodeId> {
        self.concurrency.task_context.last().copied()
    }
    pub(super) fn cancellation_has_child(&self, scope: NodeId) -> bool {
        self.concurrency.resources.iter().any(|(node, resource)| {
            resource.scope == scope
                && resource.kind == Kind::Task
                && self
                    .concurrency
                    .tasks
                    .get(node)
                    .is_none_or(|task| task.may_fail)
        })
    }
    pub(super) fn remap_concurrent_identity(&mut self, recent: NodeId, older: NodeId) {
        self.concurrency.message_flow.remap(recent, older);
        for flow in self.channel_return_states.values_mut() {
            flow.remap(recent, older);
        }
        let remap = |node: &mut NodeId| {
            if *node == recent {
                *node = older;
            }
        };
        let set = |nodes: &mut BTreeSet<NodeId>| {
            if nodes.remove(&recent) {
                nodes.insert(older);
            }
        };
        for node in self
            .concurrency
            .scopes
            .iter_mut()
            .chain(&mut self.concurrency.task_context)
        {
            remap(node);
        }
        for scopes in &mut self.concurrency.suspended_scopes {
            for node in scopes {
                remap(node);
            }
        }
        let resources = std::mem::take(&mut self.concurrency.resources);
        let alternatives = std::mem::take(&mut self.concurrency.resource_alternatives);
        for (mut node, mut resource) in
            resources
                .into_iter()
                .chain(alternatives.into_iter().flat_map(|(node, values)| {
                    values.into_iter().map(move |resource| (node, resource))
                }))
        {
            remap(&mut node);
            remap(&mut resource.scope);
            for reference in resource.task.iter_mut().chain(resource.channel.iter_mut()) {
                remap(reference);
            }
            self.concurrency.merge_resource(node, resource);
        }
        if let Some(task) = self.concurrency.tasks.remove(&recent) {
            self.concurrency
                .tasks
                .entry(older)
                .and_modify(|old| descriptors::merge_task(old, &task))
                .or_insert(task);
        }
        for task in self.concurrency.tasks.values_mut() {
            copy::remap_value_origins(&mut task.output, recent, older);
            set(&mut task.borrows);
        }
        if let Some(receiver) = self.concurrency.receivers.remove(&recent) {
            self.concurrency
                .receivers
                .entry(older)
                .and_modify(|old| descriptors::merge_value(old, &receiver))
                .or_insert(receiver);
        }
        for receiver in self.concurrency.receivers.values_mut() {
            copy::remap_value_origins(receiver, recent, older);
        }
        set(&mut self.concurrency.invalid);
        if let Some(tasks) = self.concurrency.borrowed.remove(&recent) {
            self.concurrency
                .borrowed
                .entry(older)
                .or_default()
                .extend(tasks);
        }
        for tasks in self
            .concurrency
            .borrowed
            .values_mut()
            .chain(&mut self.concurrency.clone_sources)
        {
            set(tasks);
        }
        if let Some(messages) = self.concurrency.messages.remove(&recent) {
            self.concurrency
                .messages
                .entry(older)
                .or_default()
                .extend(messages);
        }
        for messages in self.concurrency.messages.values_mut() {
            for message in messages {
                copy::remap_value_origins(message, recent, older);
            }
        }
        set(&mut self.concurrency.uncertain_messages);
        if let Some(bound) = self.concurrency.iteration_bounds.remove(&recent) {
            self.concurrency
                .iteration_bounds
                .entry(older)
                .and_modify(|old| *old = old.zip(bound).map(|(a, b)| a.max(b)))
                .or_insert(bound);
        }
        for boundary in &mut self.concurrent_boundaries {
            remap(&mut boundary.scope);
            if let Some(task) = &mut boundary.task {
                remap(task);
            }
        }
    }
    pub(super) fn concurrent_transport(&self, value: &Value) -> bool {
        !value.outer_results.is_empty()
            && value
                .outer_results
                .is_subset(&self.concurrency.transport_results)
    }
    fn concurrent_boundary(
        &mut self,
        kind: super::super::ConcurrentBoundaryKind,
        scope: NodeId,
        task: Option<NodeId>,
        span: Span,
        parents: impl IntoIterator<Item = CauseId>,
    ) {
        let cause = self.cause(
            CauseKind::Call,
            span,
            format!(
                "structured {kind:?} boundary retains owning scope and complete dependency proof"
            ),
            parents,
        );
        self.concurrent_boundaries
            .push(super::super::ConcurrentBoundary {
                span,
                scope,
                task,
                kind,
                cause,
            });
    }
    pub(super) fn concurrent_let_resource(&self, value: &Value) -> bool {
        let direct = argument(&value.ty, "Channel::Sender").is_some()
            || argument(&value.ty, "Channel::Receiver").is_some()
            || argument(&value.ty, "Channel::Detached").is_some();
        if direct
            || (!value.origins.nodes.is_empty()
                && value
                    .origins
                    .nodes
                    .iter()
                    .all(|node| self.concurrency.receivers.contains_key(node)))
        {
            return true;
        }
        let resources = self.concurrent_nodes(value);
        if resources.is_empty()
            || self.has_unresolved_row(value)
            || value.mutable_environment
            || value.observer_environment
            || (!value.construction && value.publication == Publication::Live)
        {
            return false;
        }
        let reachable = self.heap.reachable(value.origins.nodes.iter().copied());
        if reachable.iter().any(|node| {
            !resources.contains(node) && !self.heap.nodes[node.0 as usize].writable_roots.is_empty()
        }) {
            return false;
        }
        self.fields.iter().all(|((node, _), child)| {
            !reachable.contains(node)
                || ((child.publication != Publication::Live
                    || (!child.origins.nodes.is_empty()
                        && child
                            .origins
                            .nodes
                            .iter()
                            .all(|node| resources.contains(node))))
                    && !child.mutable_environment
                    && !child.observer_environment
                    && (!self.contains_resource(child) || !self.concurrent_nodes(child).is_empty()))
        })
    }
    pub(super) fn concurrent_copy_boundary(&mut self, value: &Value, span: Span) {
        if self.concurrent_nodes(value).iter().any(|node| {
            matches!(
                self.concurrency.resources[node].kind,
                Kind::Scope | Kind::Task
            )
        }) {
            self.error("E0606", span, "scope and task identities cannot be cloned through any aggregate or callable environment", [value.cause]);
        }
    }
    pub(super) fn merge_concurrent_states(&mut self, states: &[State]) {
        let Some(first) = states.first() else {
            return;
        };
        let mut merged = first.clone();
        merged.message_flow =
            messages::Flow::merge(states.iter().map(|state| state.message_flow.clone()));
        for state in &states[1..] {
            for (node, bound) in &state.iteration_bounds {
                merged
                    .iteration_bounds
                    .entry(*node)
                    .and_modify(|old| *old = old.zip(*bound).map(|(a, b)| a.max(b)))
                    .or_insert(*bound);
            }
            merged.invalid.extend(&state.invalid);
            for (node, resource) in state.resources.iter().chain(
                state
                    .resource_alternatives
                    .iter()
                    .flat_map(|(node, values)| values.iter().map(move |resource| (node, resource))),
            ) {
                merged.merge_resource(*node, resource.clone());
            }
            for (node, receiver) in &state.receivers {
                merged
                    .receivers
                    .entry(*node)
                    .and_modify(|old| descriptors::merge_value(old, receiver))
                    .or_insert_with(|| receiver.clone());
            }
            merged.transport_results.extend(&state.transport_results);
            for (node, task) in &state.tasks {
                merged
                    .tasks
                    .entry(*node)
                    .and_modify(|old| descriptors::merge_task(old, task))
                    .or_insert_with(|| task.clone());
            }
            for (node, borrows) in &state.borrowed {
                merged.borrowed.entry(*node).or_default().extend(borrows);
            }
            for (channel, messages) in &state.messages {
                if let Some(existing) = merged.messages.get_mut(channel) {
                    if existing != messages {
                        merged.uncertain_messages.insert(*channel);
                        for message in messages {
                            if !existing.contains(message) {
                                existing.push(message.clone());
                            }
                        }
                    }
                } else {
                    merged.messages.insert(*channel, messages.clone());
                }
            }
            merged.uncertain_messages.extend(&state.uncertain_messages);
        }
        self.concurrency = merged;
    }
    pub(super) fn concurrent_iteration_changes_authority(
        &self,
        before: &State,
        retained: &BTreeSet<NodeId>,
    ) -> bool {
        retained.iter().any(|node| {
            before.invalid.contains(node) != self.concurrency.invalid.contains(node)
                || before.resource_alternatives.get(node)
                    != self.concurrency.resource_alternatives.get(node)
                || before
                    .resources
                    .get(node)
                    .zip(self.concurrency.resources.get(node))
                    .is_some_and(|(old, current)| {
                        old.task != current.task || old.scope != current.scope
                    })
                || before.borrowed.get(node) != self.concurrency.borrowed.get(node)
        })
    }
    pub(super) fn register_standard_concurrent_types(&mut self) {
        let span = Span {
            file: FileId(u32::MAX),
            start: 0,
            end: 0,
        };
        for name in [
            "Concurrent::Task",
            "Channel::Sender",
            "Channel::Receiver",
            "Channel::Detached",
        ] {
            self.types.insert(
                name.into(),
                TypeDeclaration {
                    visibility: Visibility::Public,
                    is_halt: false,
                    name: name.into(),
                    generics: vec![GenericParameter {
                        hir_id: None,
                        name: "T".into(),
                        bound: None,
                        default: None,
                        span,
                    }],
                    value: None,
                    variants: vec![],
                    opaque: true,
                    nominal: false,
                    span,
                },
            );
        }
        let panic_info = Ty::Record(
            [
                ("message".into(), (false, Ty::Str)),
                (
                    "index".into(),
                    (false, Ty::Optional(Box::new(Ty::Int("int".into())))),
                ),
            ]
            .into(),
        );
        let double_fault = Ty::Record(
            [
                (
                    "primary".into(),
                    (false, Ty::Named("Concurrent::UnwindCause".into())),
                ),
                ("cleanup".into(), (false, panic_info.clone())),
            ]
            .into(),
        );
        for (owner, variants) in [
            (
                "Concurrent::TaskFault",
                vec![
                    ("Panicked", Some(panic_info.clone())),
                    ("Cancelled", None),
                    ("DoubleFaultFatal", Some(double_fault)),
                ],
            ),
            (
                "Concurrent::UnwindCause",
                vec![
                    ("Panicked", Some(panic_info)),
                    ("Cancelled", None),
                    ("EffectAborted", None),
                ],
            ),
            ("Channel::ChannelError", vec![("Closed", None)]),
        ] {
            let typing_environment = self.capture_typing_environment();
            for (variant, payload) in variants {
                let tag = format!("{owner}::{variant}");
                self.constructors.insert(
                    tag.clone(),
                    ConstructorInfo {
                        typing_environment: typing_environment.clone(),
                        source: None,
                        source_syntax: None,
                        source_type_witness: None,
                        tag,
                        owner: Ty::Named(owner.into()),
                        payload: payload.clone().unwrap_or(Ty::Unit),
                        nominal: false,
                        has_payload: payload.is_some(),
                        payload_syntax: None,
                        span,
                    },
                );
            }
        }
    }
    pub(super) fn concurrent_generic(
        &mut self,
        value: &mut Value,
        arguments: &[TypeExpr],
        span: Span,
    ) -> bool {
        if !value
            .callables
            .iter()
            .any(|target| matches!(target, Callable::Builtin(name) if name == "Channel::bounded"))
        {
            return false;
        }
        if arguments.len() != 1 {
            self.error(
                "E0340",
                span,
                "bounded requires one message type",
                [value.cause],
            );
            return true;
        }
        let ty = self.ty(&arguments[0]);
        self.require_type_argument_identity(&arguments[0]);
        let arg = self.canonical_type_argument(&arguments[0], ty);
        let endpoint = |name: &str| Ty::Applied {
            constructor: name.into(),
            arguments: vec![arg.clone()],
        };
        value.ty = Ty::Callable(
            vec![Ty::Int("int".into())],
            Box::new(Ty::Tuple(vec![
                endpoint("Channel::Sender"),
                endpoint("Channel::Receiver"),
            ])),
        );
        value.callables = vec![Callable::Builtin(format!(
            "Channel::__bounded_{}_{}_{}",
            span.file.0, span.start, span.end
        ))];
        true
    }
    pub(super) fn concurrent_receiver(
        &mut self,
        base: &Value,
        field: &str,
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        let receiver_type = self.expanded(&base.ty, &mut BTreeSet::new());
        let name = match (field, &receiver_type) {
            ("fork", Ty::Named(name)) if name == "Concurrent::Scope" => "Concurrent::fork",
            ("join", ty) if argument(ty, "Concurrent::Task").is_some() => "Concurrent::join",
            _ => return None,
        };
        let node = self.descriptor_node(span, 0x6100, frame.owner);
        let mut value = Value::reference(
            Ty::Callable(
                if field == "fork" {
                    vec![Ty::Unknown]
                } else {
                    vec![]
                },
                Box::new(Ty::Unknown),
            ),
            node,
            base.cause,
        );
        value.callables.push(Callable::Builtin(name.into()));
        self.store_field(node, Slot::Capture(0), base.clone());
        self.concurrency.receivers.insert(node, base.clone());
        value.permission = Permission::Read;
        value.publication = Publication::Immutable;
        Some(value)
    }
    fn concurrent_effect(&mut self, frame: &mut Frame, effect: &str) {
        frame.obligations.effects.insert(effect.into());
        frame.obligations.concrete_effects.insert(effect.into());
    }
    fn concurrent_nodes(&self, value: &Value) -> BTreeSet<NodeId> {
        self.heap
            .reachable(value.origins.nodes.iter().copied())
            .into_iter()
            .filter(|node| self.concurrency.resources.contains_key(node))
            .collect()
    }
    fn concurrent_resource(
        &mut self,
        ty: Ty,
        kind: Kind,
        location: (NodeId, Option<NodeId>),
        span: Span,
        frame: &Frame,
        discriminator: u32,
    ) -> Value {
        let (scope, channel) = location;
        let formal = self
            .concurrency
            .resources
            .values()
            .any(|resource| resource.formal && resource.scope == scope);
        let node = self.descriptor_node(span, discriminator, frame.owner);
        let mut value = Value::reference(ty, node, self.heap.nodes[node.0 as usize].cause);
        let node = *value.origins.nodes.first().unwrap();
        self.concurrency.resources.insert(
            node,
            Resource {
                cause: value.cause,
                scope,
                task: self.concurrency.task_context.last().copied(),
                kind,
                channel,
                formal,
            },
        );
        value.construction = true;
        value.permission = Permission::Write;
        value
    }
    fn concurrent_identity(
        &mut self,
        value: &Value,
        kind: Kind,
        span: Span,
    ) -> Option<(NodeId, Resource)> {
        if !self.require_exact_resource_nodes(value, span) {
            return None;
        }
        let identities: Vec<_> = value
            .origins
            .nodes
            .iter()
            .filter_map(|node| {
                self.concurrency
                    .resources
                    .get(node)
                    .filter(|resource| resource.kind == kind)
                    .map(|resource| (*node, resource.clone()))
            })
            .collect();
        if identities.len() != 1 {
            self.unsupported(
                span,
                "resource operation needs one verified owning scope and descriptor identity",
            );
            return None;
        }
        let (node, resource) = identities[0].clone();
        if resource.formal
            && self.concurrency.invalid.iter().any(|invalid| {
                self.concurrency
                    .resources
                    .get(invalid)
                    .is_some_and(|old| old.kind == kind)
                    && self.heap.relation(node, *invalid).disjoint != Condition::TRUE
            })
        {
            self.error(
                "E0603",
                span,
                "formal descriptor may alias authority consumed by an earlier operation",
                [value.cause],
            );
        }
        if self.concurrency.invalid.contains(&node) {
            self.error(
                "E0603",
                span,
                "descriptor authority has already been consumed",
                [value.cause],
            );
        }
        if !resource.formal && !self.concurrency.scopes.contains(&resource.scope) {
            self.error(
                "E0606",
                span,
                "resource has left its owning structured scope",
                [value.cause],
            );
        }
        Some((node, resource))
    }
    fn concurrent_escape(&mut self, value: &Value, scope: NodeId, span: Span) {
        if !self.require_exact_resource_nodes(value, span) {
            return;
        }
        if self
            .concurrent_nodes(value)
            .iter()
            .any(|node| self.concurrency.resources[node].scope == scope)
        {
            self.error(
                "E0606",
                span,
                "scope-owned authority escapes through returned data or a callable environment",
                [value.cause],
            );
        }
    }
    fn concurrent_capture_lifetime(
        &mut self,
        resource: &Resource,
        destination: NodeId,
        span: Span,
        cause: CauseId,
    ) {
        if resource.scope == destination {
            return;
        }
        let source = self
            .concurrency
            .scopes
            .iter()
            .position(|scope| *scope == resource.scope);
        let target = self
            .concurrency
            .scopes
            .iter()
            .position(|scope| *scope == destination);
        match (source, target) {
            (Some(source), Some(target)) if source <= target => {}
            (None, _) if resource.formal => self.unsupported(
                span,
                "cross-scope capture requires a caller lifetime relation for the formal descriptor",
            ),
            _ => self.error(
                "E0606",
                span,
                "child lifetime would exceed the captured descriptor's owning scope",
                [cause],
            ),
        }
    }
    fn concurrent_graph_shareable(&self, value: &Value, allow_sender: bool) -> bool {
        self.concurrent_graph_shareable_inner(value, allow_sender, &mut BTreeSet::new())
    }
    fn concurrent_graph_shareable_inner(
        &self,
        value: &Value,
        allow_sender: bool,
        seen: &mut BTreeSet<(bool, usize)>,
    ) -> bool {
        if value.mutable_environment
            || value.observer_environment
            || value.publication == Publication::Live
        {
            return false;
        }
        let allowed = |ty: &Ty| {
            argument(ty, "Channel::Detached").is_some()
                || (allow_sender && argument(ty, "Channel::Sender").is_some())
        };
        if self.resource_type(&value.ty)
            && !allowed(&value.ty)
            && self.concurrent_nodes(value).is_empty()
        {
            return false;
        }
        for node in self.heap.reachable(value.origins.nodes.iter().copied()) {
            if self.concurrency.resources.contains_key(&node) && !self.exact_resource_node(node) {
                return false;
            }
            if let Some(resource) = self.concurrency.resources.get(&node)
                && resource.kind != Kind::Detached
                && !(allow_sender && resource.kind == Kind::Sender)
            {
                return false;
            }
            for ((parent, _), field) in &self.fields {
                if *parent == node
                    && (field.mutable_environment
                        || field.observer_environment
                        || (field.publication == Publication::Live && !allowed(&field.ty))
                        || (self.resource_type(&field.ty)
                            && !allowed(&field.ty)
                            && self.concurrent_nodes(field).is_empty()))
                {
                    return false;
                }
            }
        }
        for callable in self.graph_callables(value) {
            if self.has_retained_handlers(&callable) {
                return false;
            }
            let key = match callable {
                Callable::Named(id) => (false, id),
                Callable::Closure(id) => (true, id),
                _ => continue,
            };
            if !seen.insert(key) {
                continue;
            }
            if let Some(dependencies) = self.callable_dependencies.get(&key) {
                for (&binding, &mode) in &dependencies.named {
                    if mode != Mode::Read
                        || !self.concurrent_graph_shareable_inner(
                            &self.capture_value(binding),
                            allow_sender,
                            seen,
                        )
                    {
                        return false;
                    }
                }
            }
        }
        true
    }
    fn concurrent_callable_proof(&mut self, value: &Value, span: Span) {
        for callable in self.graph_callables(value) {
            if self.has_retained_handlers(&callable) {
                self.error(
                    "E0615",
                    span,
                    "a child task cannot inherit an ancestor handler definition",
                    [value.cause],
                );
            }
            let key = match callable {
                Callable::Named(id) => (false, id),
                Callable::Closure(id) => (true, id),
                Callable::Symbolic(..) => {
                    self.unsupported(span, "callable transfer requires a complete latent environment and named-dependency proof");
                    continue;
                }
                _ => continue,
            };
            if !self.callable_dependencies.contains_key(&key) {
                self.unsupported(
                    span,
                    "callable transfer requires an instantiated latent dependency summary",
                );
            }
        }
    }
    pub(super) fn concurrent_builtin(
        &mut self,
        callee: &Value,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        if !is_builtin(name) {
            return None;
        }
        let mut bound = args.to_vec();
        if matches!(name, "Concurrent::fork" | "Concurrent::join") {
            let receivers: Vec<_> = callee
                .origins
                .nodes
                .iter()
                .filter_map(|node| self.concurrency.receivers.get(node).cloned())
                .collect();
            if receivers.len() == 1 {
                bound.insert(
                    0,
                    (
                        if name == "Concurrent::fork" {
                            ParameterMode::Mut
                        } else {
                            ParameterMode::Read
                        },
                        receivers[0].clone(),
                        span,
                    ),
                );
            } else if !receivers.is_empty() {
                self.unsupported(
                    span,
                    "conditional receiver method needs a correlated descriptor identity proof",
                );
            }
        }
        let args = bound.as_slice();
        self.concurrent_effect(
            frame,
            if name.starts_with("Concurrent::") {
                "Concurrent"
            } else {
                "Fiber"
            },
        );
        let expected = if name == "Concurrent::fork" || name == "Channel::send" {
            2
        } else {
            1
        };
        if args.len() != expected {
            self.error(
                "E0314",
                span,
                "structured operation argument count mismatch",
                [],
            );
            return Some(self.unit(span));
        }
        if name.starts_with("Concurrent::") {
            for (index, (mode, value, argument_span)) in args.iter().enumerate() {
                let expected = if name == "Concurrent::fork" && index == 0 {
                    ParameterMode::Mut
                } else {
                    ParameterMode::Read
                };
                if *mode != expected {
                    self.error(
                        "E0405",
                        *argument_span,
                        "structured operation argument reception mode mismatch",
                        [value.cause],
                    );
                }
            }
        }
        Some(match name {
            "Concurrent::scope" => self.concurrent_scope(&args[0].1, span, frame),
            "Concurrent::fork" => self.concurrent_fork(&args[0].1, &args[1].1, span, frame),
            "Concurrent::join" => self.concurrent_join(&args[0].1, span, frame),
            _ => self.concurrent_channel(callee, name, args, span, frame),
        })
    }
    fn concurrent_scope(&mut self, body: &Value, span: Span, frame: &mut Frame) -> Value {
        let outside_bindings = self.bindings.len();
        let node = self.descriptor_node(span, 0x6200, frame.owner);
        let mut scope = Value::reference(
            Ty::Named("Concurrent::Scope".into()),
            node,
            self.heap.nodes[node.0 as usize].cause,
        );
        scope.permission = Permission::Write;
        self.concurrency.resources.insert(
            node,
            Resource {
                cause: scope.cause,
                scope: node,
                task: self.concurrency.task_context.last().copied(),
                kind: Kind::Scope,
                channel: None,
                formal: false,
            },
        );
        if !self.exact_resource_node(node) {
            self.unsupported(span, "scope entry requires an individual lifetime identity");
            return self.resource_unproved(span);
        }
        self.concurrency.scopes.push(node);
        self.concurrent_boundary(
            super::super::ConcurrentBoundaryKind::Scope,
            node,
            self.concurrency.task_context.last().copied(),
            span,
            [body.cause, self.heap.nodes[node.0 as usize].cause],
        );
        let callback_context = self.concurrency.scope_callbacks.clone();
        for callable in &body.callables {
            if let Callable::Closure(id) = callable {
                self.concurrency.scope_callbacks.insert(*id);
            }
        }
        self.begin_scope_cancellation(node, span);
        let scope_recency = self.recency_moves.len();
        let mut result = self.invoke(body, vec![(ParameterMode::Mut, scope, span)], span, frame);
        if self.recency_moves[scope_recency..]
            .iter()
            .any(|(recent, _)| *recent == node)
            || self.concurrency.scopes.last() != Some(&node)
            || !self.exact_resource_node(node)
        {
            self.cancellation_contexts.pop();
            self.concurrency.scope_callbacks = callback_context;
            self.concurrency.scopes.pop();
            self.unsupported(
                span,
                "implicit scope cleanup requires the same individual lifetime identity as entry",
            );
            return self.resource_unproved(span);
        }
        self.finish_scope_cancellation(node, &mut result, span, frame);
        if self.concurrency.scopes.last() != Some(&node) || !self.exact_resource_node(node) {
            self.concurrency.scope_callbacks = callback_context;
            self.concurrency.scopes.pop();
            self.unsupported(
                span,
                "scope recovery and cleanup require an individual lifetime identity",
            );
            return self.resource_unproved(span);
        }
        self.concurrency.scope_callbacks = callback_context;
        if !matches!(result.ty, Ty::Result(_, _) | Ty::Never) {
            self.error(
                "E0301",
                span,
                "scope body must return Result<T, TaskFault>",
                [result.cause],
            );
        } else if let Ty::Result(_, error) = &result.ty {
            self.require_type(
                &Value::scalar(*error.clone(), None, result.cause),
                &Ty::Named("Concurrent::TaskFault".into()),
                span,
            );
        }
        self.concurrent_escape(&result, node, span);
        if self.has_unresolved_row(&result) {
            self.unsupported(
                span,
                "scope return needs a complete row ownership and inspection proof",
            );
        }
        let escaped: Vec<_> = self.bindings[..outside_bindings]
            .iter()
            .filter(|binding| binding.alive)
            .map(|binding| binding.value.clone())
            .collect();
        for retained in escaped {
            self.concurrent_escape(&retained, node, span);
        }
        let task_nodes: BTreeSet<_> = self
            .concurrency
            .resources
            .keys()
            .filter_map(|id| {
                self.concurrency
                    .resource_variants(*id)
                    .any(|resource| resource.scope == node && resource.kind == Kind::Task)
                    .then_some(*id)
            })
            .collect();
        if result.ty != Ty::Never && result.result_tag != Some(false) {
            for task in &task_nodes {
                let record = &self.concurrency.tasks[task];
                if !record.observed
                    && record.output.results.iter().any(|id| {
                        let duty = &self.result_duties[*id as usize];
                        !duty.inspected && !duty.abnormal
                    })
                {
                    self.error(
                        "E0720",
                        span,
                        "successful scope exit abandons an unjoined task's business Result",
                        [record.output.cause],
                    );
                }
            }
            let channels: BTreeSet<_> = self
                .concurrency
                .resources
                .keys()
                .flat_map(|id| self.concurrency.resource_variants(*id))
                .filter(|resource| resource.scope == node)
                .filter_map(|resource| resource.channel)
                .collect();
            for channel in channels {
                self.channel_unread_results(channel, Some(&result), span);
            }
        }
        let terminal_tasks: BTreeSet<_> = task_nodes
            .iter()
            .copied()
            .filter(|task| {
                self.concurrency
                    .resource_variants(*task)
                    .all(|resource| resource.kind == Kind::Task && resource.scope == node)
            })
            .collect();
        for borrows in self.concurrency.borrowed.values_mut() {
            borrows.retain(|task| !terminal_tasks.contains(task));
        }
        self.channel_scope_exit(node, &result, span, frame);
        self.concurrency.scopes.pop();
        if let Ty::Result(ok, _) = &result.ty {
            let error = Ty::Named("Concurrent::TaskFault".into());
            result.ty = Ty::Result(ok.clone(), Box::new(error.clone()));
            result.result_tag = None;
            result.result_payload = None;
            result.result_error = Some(Box::new(self.standard_value(
                error,
                span,
                frame.owner,
                0x6210,
            )));
        }
        result
    }
    fn concurrent_fork(
        &mut self,
        scope: &Value,
        action: &Value,
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        if !self.require_exact_resource_nodes(action, span) {
            return self.resource_unproved(span);
        }
        let Some((scope_node, scope_resource)) = self.concurrent_identity(scope, Kind::Scope, span)
        else {
            return self.resource_unproved(span);
        };
        if scope.permission != Permission::Write {
            self.error(
                "E0603",
                span,
                "fork requires the writable scope borrow",
                [scope.cause],
            );
        }
        self.access(scope, None, Mode::Write, span, frame);
        let before_bindings = self.bindings.len();
        let task_node = self.descriptor_node(span, 0x6300, frame.owner);
        if self.heap.nodes[task_node.0 as usize].multiplicity != Multiplicity::One {
            self.unsupported(span, "fork requires an individual child identity");
            return self.resource_unproved(span);
        }
        let task_recency = self.recency_moves.len();
        let mut borrows = BTreeSet::new();
        for node in self.concurrent_nodes(action) {
            let resource = self.concurrency.resources[&node].clone();
            self.concurrent_capture_lifetime(&resource, scope_resource.scope, span, action.cause);
            match resource.kind {
                Kind::Sender => {
                    borrows.insert(node);
                }
                Kind::Detached => {
                    if self.concurrency.invalid.contains(&node)
                        || resource.task != self.concurrency.task_context.last().copied()
                    {
                        self.error(
                            "E0603",
                            span,
                            "child transfer cannot reuse consumed or foreign detached authority",
                            [action.cause],
                        );
                    }
                    self.concurrency.resources.get_mut(&node).unwrap().task = Some(task_node);
                }
                _ => self.error(
                    "E0601",
                    span,
                    "child captures non-transferable scope, task, or resource authority",
                    [action.cause],
                ),
            }
        }
        if self
            .graph_callables(action)
            .iter()
            .any(|callable| self.has_retained_handlers(callable))
        {
            self.error(
                "E0615",
                span,
                "a child task cannot inherit an ancestor handler definition",
                [action.cause],
            );
        }
        if !self.concurrent_graph_shareable(action, true) {
            self.error(
                "E0601",
                span,
                "child callback captures live data or a non-transferable resource",
                [action.cause],
            );
        }
        if self.has_unresolved_row(action) {
            self.unsupported(
                span,
                "child capture needs an instantiated row environment proof",
            );
        }
        let outside_handlers = std::mem::take(&mut self.active_handlers);
        let outside_budget = std::mem::take(&mut self.budget_coverage);
        let mut child_scopes = self.concurrency.scopes.clone();
        if let Some(index) = child_scopes
            .iter()
            .position(|scope| *scope == scope_resource.scope)
        {
            child_scopes.truncate(index + 1);
        } else {
            child_scopes = vec![scope_resource.scope];
        }
        let parent_scopes = std::mem::replace(&mut self.concurrency.scopes, child_scopes);
        self.concurrency.suspended_scopes.push(parent_scopes);
        self.channel_task_order(task_node, true, span, frame);
        self.concurrency.task_context.push(task_node);
        self.concurrency.clone_sources.push(borrows.clone());
        let mut child = self.frame(frame.env.clone(), true);
        self.scopes.set_parent(child.owner, frame.owner);
        let mut output = self.invoke(action, vec![], span, &mut child);
        self.concurrency.clone_sources.pop();
        self.concurrency.task_context.pop();
        self.concurrency.scopes = self
            .concurrency
            .suspended_scopes
            .pop()
            .expect("fork preserves its parent's active scope context");
        self.active_handlers = outside_handlers;
        if child
            .obligations
            .selected_handlers
            .iter()
            .any(|id| self.active_handlers.contains(id))
        {
            self.error(
                "E0615",
                span,
                "a child task selected a handler from its ancestor task",
                [action.cause],
            );
        }
        self.budget_coverage = outside_budget;
        if self.recency_moves[task_recency..]
            .iter()
            .any(|(recent, _)| *recent == task_node)
            || self.heap.nodes[task_node.0 as usize].multiplicity != Multiplicity::One
        {
            self.unsupported(
                span,
                "child completion requires its original individual task identity",
            );
            return self.resource_unproved(span);
        }
        for (&binding, &mode) in &child.obligations.named {
            if binding < before_bindings {
                let dependency = self.capture_value(binding);
                if !self.require_exact_resource_nodes(&dependency, span) {
                    continue;
                }
                for node in self.concurrent_nodes(&dependency) {
                    let resource = self.concurrency.resources[&node].clone();
                    self.concurrent_capture_lifetime(
                        &resource,
                        scope_resource.scope,
                        span,
                        dependency.cause,
                    );
                    if self.concurrency.resources[&node].kind == Kind::Sender {
                        borrows.insert(node);
                    }
                }
                if mode != Mode::Read || !self.concurrent_graph_shareable(&dependency, true) {
                    self.error(
                        "E0601",
                        span,
                        "child callee, handler, or cleanup depends on outside live state",
                        [dependency.cause],
                    );
                }
            }
        }
        for access in self.current_accesses(&child.obligations.accesses) {
            if access.mode != Mode::Read
                && access.origins.nodes.iter().any(|node| {
                    !self.access_is_local(&access, *node, child.owner)
                        && self
                            .concurrency
                            .resources
                            .get(node)
                            .is_none_or(|resource| resource.task != Some(task_node))
                })
            {
                self.error(
                    "E0601",
                    access.span,
                    "child writes storage owned by its parent task",
                    [access.cause],
                );
            }
        }
        if child
            .obligations
            .effects
            .iter()
            .any(|effect| !matches!(effect.as_str(), "Fiber" | "Concurrent"))
        {
            self.error(
                "E0615",
                span,
                "child user effects and Div exhaustion require child-local handlers",
                [action.cause],
            );
        }
        if child.obligations.symbolic {
            self.unsupported(
                span,
                "child callback needs a complete transitive dependency and effect proof",
            );
        }
        self.concurrent_boundary(
            super::super::ConcurrentBoundaryKind::Fork,
            scope_node,
            Some(task_node),
            span,
            std::iter::once(action.cause)
                .chain(child.obligations.accesses.iter().map(|access| access.cause))
                .collect::<Vec<_>>(),
        );
        if self.has_unresolved_row(&output) {
            self.unsupported(
                span,
                "task return needs a complete row ownership and inspection proof",
            );
        }
        self.concurrent_callable_proof(&output, span);
        if !self.require_exact_resource_nodes(&output, span) {
            return self.resource_unproved(span);
        }
        if !self.concurrent_graph_shareable(&output, false) && output.ty != Ty::Never {
            self.error(
                "E0601",
                span,
                "task result must be immutable data or admitted detached authority",
                [output.cause],
            );
        }
        for node in self.concurrent_nodes(&output) {
            if self.concurrency.invalid.contains(&node) {
                self.error(
                    "E0603",
                    span,
                    "task output cannot restore a consumed descriptor",
                    [output.cause],
                );
            }
            if self.concurrency.resources[&node].kind != Kind::Detached {
                self.error(
                    "E0606",
                    span,
                    "task result exposes non-transferable authority",
                    [output.cause],
                );
            }
        }
        if !self.contains_resource(&output) {
            freeze_formal_value(&mut output);
        }
        frame.obligations.include(&child.obligations, false);
        for node in &borrows {
            self.concurrency
                .borrowed
                .entry(*node)
                .or_default()
                .insert(task_node);
        }
        self.concurrency.resources.insert(
            task_node,
            Resource {
                cause: self.heap.nodes[task_node.0 as usize].cause,
                scope: scope_resource.scope,
                task: self.concurrency.task_context.last().copied(),
                kind: Kind::Task,
                channel: None,
                formal: scope_resource.formal,
            },
        );
        self.concurrency.tasks.insert(
            task_node,
            Task {
                output: output.clone(),
                may_fail: !self.nonfaulting_literal_child(action),
                joined: false,
                observed: false,
                borrows,
            },
        );
        let mut task = Value::reference(
            self.concurrent_applied("Concurrent::Task", output.ty.clone()),
            task_node,
            output.cause,
        );
        task.permission = Permission::Read;
        task.publication = Publication::Immutable;
        task.construction = false;
        task
    }
    fn concurrent_join(&mut self, task: &Value, span: Span, frame: &mut Frame) -> Value {
        let Some((node, resource)) = self.concurrent_identity(task, Kind::Task, span) else {
            return self.resource_unproved(span);
        };
        if resource.task != self.concurrency.task_context.last().copied() {
            self.error(
                "E0606",
                span,
                "task handle cannot cross task ownership",
                [task.cause],
            );
        }
        let Some(record) = self.concurrency.tasks.get(&node).cloned() else {
            return self.unit(span);
        };
        if record.joined {
            self.error(
                "E0603",
                span,
                "task result may be joined only once",
                [task.cause],
            );
        }
        self.concurrent_boundary(
            super::super::ConcurrentBoundaryKind::Join,
            resource.scope,
            Some(node),
            span,
            [task.cause, record.output.cause],
        );
        self.concurrency.tasks.get_mut(&node).unwrap().joined = true;
        self.concurrency.tasks.get_mut(&node).unwrap().observed = true;
        self.channel_task_order(node, false, span, frame);
        self.concurrency.invalid.insert(node);
        for source in record.borrows {
            if let Some(borrowers) = self.concurrency.borrowed.get_mut(&source) {
                borrowers.remove(&node);
            }
        }
        let owners: BTreeSet<_> = record
            .output
            .results
            .iter()
            .map(|id| self.result_duties[*id as usize].owner)
            .collect();
        for owner in owners {
            self.transfer_results(&record.output, owner, frame.owner);
        }
        let mut output = record.output;
        let descriptors = self.concurrent_nodes(&output);
        if !descriptors.is_empty() {
            if descriptors.len() == 1 && argument(&output.ty, "Channel::Detached").is_some() {
                let descriptor_node = *descriptors.first().unwrap();
                let descriptor = self.concurrency.resources[&descriptor_node].clone();
                self.concurrency.invalid.insert(descriptor_node);
                output = self.concurrent_resource(
                    output.ty.clone(),
                    Kind::Detached,
                    (descriptor.scope, descriptor.channel),
                    span,
                    frame,
                    0x6311,
                );
            } else {
                self.unsupported(span, "task result aggregate transfer requires separate one-use receiver authority for every nested descriptor");
            }
        }
        let error = Ty::Named("Concurrent::TaskFault".into());
        let mut result = self.make_result(true, output.clone(), span, frame.owner);
        // A child's abnormal completion is contained by this ordinary Result.
        // Cancellation of the joining parent remains a separate control exit.
        result.abnormal = false;
        result.ty = Ty::Result(Box::new(output.ty), Box::new(error.clone()));
        result.result_tag = None;
        result.result_payload = None;
        result.result_error = Some(Box::new(self.standard_value(
            error,
            span,
            frame.owner,
            0x6310,
        )));
        self.concurrency
            .transport_results
            .extend(&result.outer_results);
        self.complete_carrier_source_type(&mut result, span);
        result
    }
    fn channel_result(&mut self, payload: Value, span: Span, frame: &Frame) -> Value {
        let error = Ty::Named("Channel::ChannelError".into());
        let ty = Ty::Result(Box::new(payload.ty.clone()), Box::new(error.clone()));
        let mut result = self.make_result(true, payload, span, frame.owner);
        result.ty = ty;
        result.source_type_witness = None;
        result.result_tag = None;
        result.result_payload = None;
        result.result_error = Some(Box::new(self.standard_value(
            error,
            span,
            frame.owner,
            0x6800,
        )));
        self.concurrency
            .transport_results
            .extend(&result.outer_results);
        self.complete_carrier_source_type(&mut result, span);
        result
    }
    fn endpoint_owner(
        &mut self,
        node: NodeId,
        resource: &Resource,
        consuming: bool,
        span: Span,
        cause: CauseId,
    ) {
        let clone_source = self
            .concurrency
            .clone_sources
            .iter()
            .any(|sources| sources.contains(&node));
        if clone_source || resource.task != self.concurrency.task_context.last().copied() {
            self.error("E0603", span, "endpoint authority belongs to another task; a child Sender capture permits only cloning", [cause]);
        }
        if consuming
            && self
                .concurrency
                .borrowed
                .get(&node)
                .is_some_and(|tasks| !tasks.is_empty())
        {
            self.error("E0603", span, "endpoint owner remains borrowed until every borrowing task is joined or the scope barrier completes", [cause]);
        }
    }
    fn endpoint_exclusive(&mut self, value: &Value, node: NodeId, span: Span) {
        let mut allowed = value.sources.clone();
        let mut pending: Vec<_> = allowed.iter().copied().collect();
        while let Some(id) = pending.pop() {
            for ancestor in &self.bindings[id].forwarded {
                if allowed.insert(*ancestor) {
                    pending.push(*ancestor);
                }
            }
        }
        if self.bindings.iter().enumerate().any(|(id, binding)| {
            binding.alive
                && !allowed.contains(&id)
                && self.concurrent_nodes(&binding.value).contains(&node)
        }) {
            self.error("E0603", span, "detach requires exclusive endpoint authority without a surviving alias, view, or capture", [value.cause]);
        }
    }
    fn channel_unread_results(&mut self, channel: NodeId, returned: Option<&Value>, span: Span) {
        let pending: Vec<_> = self
            .concurrency
            .messages
            .get(&channel)
            .into_iter()
            .flatten()
            .flat_map(|value| value.results.iter().copied())
            .filter(|id| {
                if self.channel_known_producer(*id) {
                    return false;
                }
                let duty = &self.result_duties[*id as usize];
                !duty.inspected
                    && !duty.abnormal
                    && !duty.covered
                    && returned.is_none_or(|value| !value.results.contains(id))
            })
            .collect();
        if let Some(id) = pending.first() {
            self.error(
                "E0720",
                span,
                "normal receiver close or scope exit loses an uninspected Result message",
                [self.result_duties[*id as usize].cause],
            );
        }
    }
    pub(super) fn concurrent_clone_sender(
        &mut self,
        source: &Value,
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        argument(
            &self.expanded(&source.ty, &mut BTreeSet::new()),
            "Channel::Sender",
        )?;
        use super::super::resource_copy::*;
        self.concurrent_effect(frame, "Fiber");
        let source_snapshot = self.copy_value_snapshot(source);
        let descriptor = |node, resource: &Resource| ResourceDescriptor {
            origin: node,
            scope: resource.scope,
            task: resource.task,
            channel: resource.channel,
            formal: resource.formal,
        };
        let (output, source_descriptor, boundary) =
            match self.concurrent_identity(source, Kind::Sender, span) {
                Some((node, resource)) => {
                    self.concurrent_boundary(
                        super::super::ConcurrentBoundaryKind::CloneSender,
                        resource.scope,
                        self.concurrency.task_context.last().copied(),
                        span,
                        [source.cause],
                    );
                    let proof = self.concurrent_boundaries.last().cloned();
                    self.deep_read(source, span, frame);
                    let output = self.concurrent_resource(
                        source.ty.clone(),
                        Kind::Sender,
                        (resource.scope, resource.channel),
                        span,
                        frame,
                        0x6700,
                    );
                    (output, Some(descriptor(node, &resource)), proof)
                }
                None => (self.resource_unproved(span), None, None),
            };
        let output_descriptor = output.origins.nodes.first().and_then(|node| {
            self.concurrency
                .resources
                .get(node)
                .filter(|resource| resource.kind == Kind::Sender)
                .map(|resource| descriptor(*node, resource))
        });
        let channel = source_descriptor.as_ref().and_then(|source| {
            source.channel.map(ResourceChannel::Known).or_else(|| {
                source
                    .formal
                    .then_some(ResourceChannel::FromSourceDescriptor(source.origin))
            })
        });
        let id = ResourceCloneId(self.resource_clones.len() as u32);
        let invocation = self.copy_invocation_stack.last().copied();
        let anchor_nodes: BTreeSet<_> = source_descriptor
            .iter()
            .chain(&output_descriptor)
            .flat_map(|resource| {
                std::iter::once(resource.scope)
                    .chain(resource.task)
                    .chain(resource.channel)
            })
            .collect();
        let anchors = anchor_nodes
            .into_iter()
            .map(|origin| super::super::copy_contract::CopyNode {
                origin,
                fact: self.heap.nodes[origin.0 as usize].clone(),
                fields: self
                    .fields
                    .iter()
                    .filter(|((parent, _), _)| *parent == origin)
                    .map(|((_, slot), value)| (slot.clone(), value.clone()))
                    .collect(),
                length: self.array_lengths.get(&origin).copied(),
                fixed: self.fixed_arrays.contains(&origin),
            })
            .collect();
        let event = ResourceCloneEvent {
            id,
            owner: frame.definition,
            lexical_owner: frame.callable_owner,
            invocation,
            source_event: self.application_effect.current_call_event(),
            span,
            contract: ResourceCloneContract::Sender,
            required_effect: ResourceCloneEffect::Fiber,
            effect_registered: frame.obligations.effects.contains("Fiber"),
            source: source_snapshot,
            source_descriptor,
            output: self.copy_value_snapshot(&output),
            output_descriptor,
            channel,
            boundary,
            anchors,
        };
        self.resource_clones.push(event);
        if let Some(call) = invocation {
            self.copy_invocations[call.0 as usize]
                .resource_copies
                .push(id);
        }
        Some(output)
    }
    fn concurrent_channel(
        &mut self,
        callee: &Value,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        if name == "Channel::bounded" || name.starts_with("Channel::__bounded_") {
            self.require_type(&args[0].1, &Ty::Int("int".into()), args[0].2);
            if args[0].0 != ParameterMode::Read {
                self.error(
                    "E0405",
                    span,
                    "channel capacity is received read-only",
                    [args[0].1.cause],
                );
            }
            let Some(scope) = self.concurrency.scopes.last().copied() else {
                self.error(
                    "E0606",
                    span,
                    "channel endpoints require an owning structured scope",
                    [],
                );
                return self.unit(span);
            };
            let Ty::Callable(_, result) = &callee.ty else {
                self.unsupported(span, "bounded channel needs an instantiated message type");
                return self.unit(span);
            };
            let Ty::Tuple(types) = &**result else {
                return self.unit(span);
            };
            if types.len() != 2 {
                return self.unit(span);
            }
            let channel = self.descriptor_node(span, 0x6400, frame.owner);
            let sender = self.concurrent_resource(
                types[0].clone(),
                Kind::Sender,
                (scope, Some(channel)),
                span,
                frame,
                0x6401,
            );
            let receiver = self.concurrent_resource(
                types[1].clone(),
                Kind::Receiver,
                (scope, Some(channel)),
                span,
                frame,
                0x6402,
            );
            self.concurrency.messages.insert(channel, vec![]);
            self.concurrent_boundary(
                super::super::ConcurrentBoundaryKind::ChannelCreate,
                scope,
                self.concurrency.task_context.last().copied(),
                span,
                [sender.cause, receiver.cause],
            );
            let mut tuple = Value::reference(*result.clone(), channel, sender.cause);
            tuple.permission = Permission::Write;
            self.store_field(channel, Slot::Tuple(0), sender);
            self.store_field(channel, Slot::Tuple(1), receiver);
            return tuple;
        }
        let mut source_value = args[0].1.clone();
        source_value.ty = self.expanded(&source_value.ty, &mut BTreeSet::new());
        let source = &source_value;
        let kind = if argument(&source.ty, "Channel::Sender").is_some() {
            Kind::Sender
        } else if argument(&source.ty, "Channel::Receiver").is_some() {
            Kind::Receiver
        } else if argument(&source.ty, "Channel::Detached").is_some() {
            Kind::Detached
        } else {
            self.error(
                "E0908",
                span,
                "channel operation requires its exact endpoint or detached descriptor resource",
                [source.cause],
            );
            return self.unit(span);
        };
        if (name == "Channel::send" && kind != Kind::Sender)
            || (name == "Channel::recv" && kind != Kind::Receiver)
            || (name == "Channel::attach" && kind != Kind::Detached)
            || (matches!(name, "Channel::detach" | "Channel::close") && kind == Kind::Detached)
        {
            self.error(
                "E0908",
                span,
                "channel operation received the wrong resource kind",
                [source.cause],
            );
            return self.unit(span);
        }
        let Some((node, resource)) = self.concurrent_identity(source, kind, span) else {
            return self.resource_unproved(span);
        };
        let writes = matches!(name, "Channel::send" | "Channel::recv" | "Channel::detach");
        let expected_mode = if writes {
            ParameterMode::Mut
        } else {
            ParameterMode::Read
        };
        if args[0].0 != expected_mode {
            self.error(
                "E0405",
                span,
                "channel operation argument reception mode mismatch",
                [source.cause],
            );
        }
        if writes && source.permission != Permission::Write {
            self.error(
                "E0603",
                span,
                "channel operation requires writable endpoint authority",
                [source.cause],
            );
        }
        self.endpoint_owner(
            node,
            &resource,
            matches!(name, "Channel::detach" | "Channel::close"),
            span,
            source.cause,
        );
        self.access(
            source,
            None,
            if writes { Mode::Write } else { Mode::Read },
            span,
            frame,
        );
        let boundary = match name {
            "Channel::send" => super::super::ConcurrentBoundaryKind::Send,
            "Channel::recv" => super::super::ConcurrentBoundaryKind::Receive,
            "Channel::detach" => super::super::ConcurrentBoundaryKind::Detach,
            "Channel::attach" => super::super::ConcurrentBoundaryKind::Attach,
            "Channel::close" => super::super::ConcurrentBoundaryKind::Close,
            _ => unreachable!(),
        };
        self.concurrent_boundary(
            boundary,
            resource.scope,
            self.concurrency.task_context.last().copied(),
            span,
            args.iter().map(|(_, value, _)| value.cause),
        );
        match name {
            "Channel::detach" => {
                self.endpoint_exclusive(source, node, span);
                self.concurrency.invalid.insert(node);
                self.concurrent_resource(
                    self.concurrent_applied("Channel::Detached", source.ty.clone()),
                    Kind::Detached,
                    (resource.scope, resource.channel),
                    span,
                    frame,
                    0x6500,
                )
            }
            "Channel::attach" => {
                let endpoint = argument(&source.ty, "Channel::Detached").unwrap();
                let kind = if argument(&endpoint, "Channel::Sender").is_some() {
                    Kind::Sender
                } else if argument(&endpoint, "Channel::Receiver").is_some() {
                    Kind::Receiver
                } else {
                    self.error(
                        "E0908",
                        span,
                        "detached resource must describe a Sender or Receiver",
                        [source.cause],
                    );
                    return self.unit(span);
                };
                self.concurrency.invalid.insert(node);
                self.concurrent_resource(
                    endpoint,
                    kind,
                    (resource.scope, resource.channel),
                    span,
                    frame,
                    0x6501,
                )
            }
            "Channel::close" => {
                if kind == Kind::Receiver {
                    self.channel_receiver_exit(node, &resource, source, span, frame);
                    if let Some(channel) = resource.channel {
                        self.channel_unread_results(channel, None, span);
                    }
                }
                self.concurrency.invalid.insert(node);
                self.unit(span)
            }
            "Channel::send" => {
                let payload = &args[1].1;
                if !self.require_exact_resource_nodes(payload, span) {
                    return self.resource_unproved(span);
                }
                self.concurrent_callable_proof(payload, span);
                let ty = argument(&source.ty, "Channel::Sender").unwrap();
                self.require_type(payload, &ty, args[1].2);
                if args[1].0 != ParameterMode::Read {
                    self.error(
                        "E0405",
                        span,
                        "message transfer uses ordinary argument reception",
                        [payload.cause],
                    );
                }
                if self.has_unresolved_row(payload) {
                    self.unsupported(
                        span,
                        "message transfer needs an instantiated row payload proof",
                    );
                }
                if !self.concurrent_graph_shareable(payload, false) {
                    self.error(
                        "E0602",
                        span,
                        "message payload contains live data or non-transferable authority",
                        [payload.cause],
                    );
                }
                for descriptor in self.concurrent_nodes(payload) {
                    let transferred = self.concurrency.resources[&descriptor].clone();
                    if transferred.kind != Kind::Detached {
                        self.error(
                            "E0602",
                            span,
                            "only detached endpoint descriptors may be sent",
                            [payload.cause],
                        );
                    }
                    if self.concurrency.invalid.contains(&descriptor)
                        || transferred.task != self.concurrency.task_context.last().copied()
                    {
                        self.error(
                            "E0603",
                            span,
                            "sent descriptor was consumed or belongs to another task",
                            [payload.cause],
                        );
                    }
                    let source_scope = self
                        .concurrency
                        .scopes
                        .iter()
                        .position(|scope| *scope == transferred.scope);
                    let destination_scope = self
                        .concurrency
                        .scopes
                        .iter()
                        .position(|scope| *scope == resource.scope);
                    if source_scope
                        .zip(destination_scope)
                        .is_none_or(|(source, destination)| source > destination)
                    {
                        self.error(
                            "E0606",
                            span,
                            "endpoint transfer cannot leave its owning scope descendants",
                            [payload.cause],
                        );
                    }
                    self.concurrency.invalid.insert(descriptor);
                }
                self.deep_read(payload, span, frame);
                if let Some(channel) = resource.channel {
                    self.concurrency
                        .messages
                        .entry(channel)
                        .or_default()
                        .push(payload.clone());
                }
                let unit = self.unit(span);
                let transport = self.channel_result(unit, span, frame);
                self.channel_record_send(
                    messages::MessageObservation {
                        endpoint: node,
                        resource: &resource,
                        source,
                        payload,
                        transport: &transport,
                    },
                    span,
                    frame,
                );
                transport
            }
            "Channel::recv" => {
                let ty = argument(&source.ty, "Channel::Receiver").unwrap();
                if resource
                    .channel
                    .is_some_and(|channel| self.concurrency.uncertain_messages.contains(&channel))
                    && self.resource_type(&ty)
                {
                    self.unsupported(span, "conditional message multiplicity requires correlated transfer and Result inspection coverage");
                }
                let mut payload = self.channel_receive_value(node, &resource, &ty, span, frame);
                payload.ty = ty;
                if !self.require_exact_resource_nodes(&payload, span) {
                    return self.resource_unproved(span);
                }
                if self.has_unresolved_row(&payload) {
                    self.unsupported(
                        span,
                        "message reception needs a complete row ownership and inspection proof",
                    );
                }
                let descriptors = self.concurrent_nodes(&payload);
                if !descriptors.is_empty() {
                    // Every receive has fresh ticket authority. Keeping sender-side
                    // aliases on the old node is essential to linear invalidation.
                    if descriptors.len() == 1
                        && argument(&payload.ty, "Channel::Detached").is_some()
                    {
                        let descriptor =
                            self.concurrency.resources[descriptors.first().unwrap()].clone();
                        payload = self.concurrent_resource(
                            payload.ty.clone(),
                            Kind::Detached,
                            (descriptor.scope, descriptor.channel),
                            span,
                            frame,
                            0x6601,
                        );
                    } else {
                        self.unsupported(span, "aggregate descriptor reception needs a correlated one-use transfer graph");
                    }
                }
                if !self.contains_resource(&payload) {
                    freeze_formal_value(&mut payload);
                }
                let transport = self.channel_result(payload.clone(), span, frame);
                self.channel_record_receive(
                    messages::MessageObservation {
                        endpoint: node,
                        resource: &resource,
                        source,
                        payload: &payload,
                        transport: &transport,
                    },
                    span,
                    frame,
                );
                transport
            }
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn check(source: &str) -> crate::sema::AnalyzeOutcome {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        crate::sema::analyze(&parsed.program, FileId(0))
    }
    #[test]
    fn outer_fork_cannot_capture_resources_from_a_shorter_inner_scope() {
        for capture in [
            "let (tx,rx)=Channel::bounded<int>(1); outer.fork(\\->{let local=clone(tx);Channel::close(local)});Channel::close(rx);",
            "let (tx,mut rx)=Channel::bounded<int>(1);let ticket=Channel::detach(mut rx);outer.fork(\\->{let local=Channel::attach(ticket);Channel::close(local)});Channel::close(tx);",
        ] {
            let result = check(&format!(
                "fn example()->Result<(),Concurrent::TaskFault> @Async {{Concurrent::scope \\mut outer -> {{let nested=Concurrent::scope \\mut inner -> {{let own=inner.fork(\\->());{capture}assert(own.join() is Ok());Ok()}};assert(nested is Ok());Ok()}}}}"
            ));
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0606"),
                "{capture}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
    #[test]
    fn outer_descriptors_may_be_borrowed_by_shorter_inner_children() {
        let result = check(
            "fn example()->Result<(),Concurrent::TaskFault> @Async {Concurrent::scope \\mut outer -> {let own=outer.fork(\\->());let (tx,rx)=Channel::bounded<int>(1);let nested=Concurrent::scope \\mut inner -> {let task=inner.fork(\\->{let local=clone(tx);Channel::close(local)});task.join()};assert(nested is Ok());Channel::close(tx);Channel::close(rx);own.join()}}",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let result = check(
            "fn example()->Result<(),Concurrent::TaskFault> @Async {Concurrent::scope \\mut outer -> {let nested=Concurrent::scope \\mut inner -> {let own=inner.fork(\\->());let task=outer.fork(\\->{let (tx,rx)=Channel::bounded<int>(1);Channel::close(tx);Channel::close(rx)});assert(own.join() is Ok());task.join()};assert(nested is Ok());Ok()}}",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn readonly_scope_paths_do_not_recover_the_original_fork_permission() {
        for source in [
            "fn example()->Result<(),Concurrent::TaskFault> @Concurrent {Concurrent::scope \\mut s -> {let view alias=s;let child=alias.fork(\\->());child.join()}}",
            "fn example()->Result<(),Concurrent::TaskFault> @Concurrent {Concurrent::scope \\mut s -> {let wrapper=.{scope:s};let child=wrapper.scope.fork(\\->());child.join()}}",
            "fn borrow(s:Concurrent::Scope)->Result<(),Concurrent::TaskFault> @Concurrent {let child=s.fork(\\->());child.join()}\nfn example()->Result<(),Concurrent::TaskFault> @Concurrent {Concurrent::scope \\mut s -> borrow(s)}",
        ] {
            let result = check(source);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0603"),
                "{:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
    #[test]
    fn separate_children_retain_separate_sender_borrows_through_returned_callbacks() {
        for (completion, accepted) in [
            (
                "assert(first.join() is Ok());assert(second.join() is Ok());Channel::close(tx);",
                true,
            ),
            (
                "assert(first.join() is Ok());Channel::close(tx);assert(second.join() is Ok());",
                false,
            ),
        ] {
            let source = format!(
                "fn callback(sender:Channel::Sender<int>)->(fn()->() @Fiber) &capture {{\\->{{let own=clone(sender);Channel::close(own)}}}}\nfn example()->Result<(),Concurrent::TaskFault> @Async {{Concurrent::scope \\mut s -> {{let (tx,rx)=Channel::bounded<int>(1);let wrapped=.{{deep:.{{produce:callback(tx)}}}};let first=s.fork(wrapped.deep.produce);let second=s.fork(wrapped.deep.produce);{completion}Channel::close(rx);Ok()}}}}"
            );
            let result = check(&source);
            if accepted {
                assert!(
                    result.program.is_some(),
                    "{:?} {:?}",
                    result.diagnostics,
                    result.unsupported
                );
            } else {
                assert!(
                    result
                        .diagnostics
                        .iter()
                        .any(|diagnostic| diagnostic.code == "E0603"),
                    "{:?} {:?}",
                    result.diagnostics,
                    result.unsupported
                );
            }
        }
    }
    #[test]
    fn repeated_detach_at_one_callsite_never_restores_the_original_endpoint() {
        for body in [
            "for 0..2 as index {let ticket=Channel::detach(mut rx);let local=Channel::attach(ticket);Channel::close(local)}",
            "let mut act=\\-> {let ticket=Channel::detach(mut rx);let local=Channel::attach(ticket);Channel::close(local)};act();act()",
        ] {
            let result = check(&format!(
                "fn example()->Result<(),Concurrent::TaskFault> @Async {{Concurrent::scope \\mut s -> {{let child=s.fork(\\->());let (tx,mut rx)=Channel::bounded<int>(1);{body};Channel::close(tx);assert(child.join() is Ok());Ok()}}}}"
            ));
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0603"),
                "repeated consumption not rejected with its authority proof: {body}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
    #[test]
    fn dynamic_scope_selection_never_chooses_one_possible_owner_as_proof() {
        for action in [
            "\\->1",
            "\\->{let local=Channel::attach(ticket);Channel::close(local);1}",
        ] {
            let result = check(&format!(
                "fn example(choice:bool)->Result<(),Concurrent::TaskFault> @Async {{Concurrent::scope \\mut outer -> {{let a=outer.fork(\\->());let nested=Concurrent::scope \\mut inner -> {{let b=inner.fork(\\->());let (tx,mut rx)=Channel::bounded<int>(1);let ticket=Channel::detach(mut rx);let task=(if choice {{outer}} else {{inner}}).fork({action});Channel::close(tx);assert(b.join() is Ok());Ok(task)}};assert(nested is Ok(_));a.join()}}}}"
            ));
            assert!(
                result.program.is_none(),
                "ambiguous scope receiver was accepted"
            );
            assert!(
                result
                    .unsupported
                    .iter()
                    .any(|proof| proof.description.contains("one verified owning scope")),
                "{:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
    #[test]
    fn proven_single_iteration_and_terminal_last_can_consume_outside_authority() {
        for prefix in ["for [0] as index", "for 0..1 as index", "loop"] {
            let stop = if prefix == "loop" { "last;" } else { "" };
            let result = check(&format!(
                "fn example()->Result<(),Concurrent::TaskFault> @Async {{Concurrent::scope \\mut s -> {{let child=s.fork(\\->());let (tx,mut rx)=Channel::bounded<int>(1);{prefix} {{let ticket=Channel::detach(mut rx);let local=Channel::attach(ticket);Channel::close(local);{stop}}};Channel::close(tx);child.join()}}}}"
            ));
            assert!(
                result.program.is_some(),
                "{prefix}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
        let result = check(
            "fn example(choice:bool)->Result<(),Concurrent::TaskFault> @Async {Concurrent::scope \\mut s -> {let child=s.fork(\\->());let (tx,rx)=Channel::bounded<int>(1);loop {Channel::close(rx);if choice {last}else{last}};Channel::close(tx);child.join()}}",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn repeated_fresh_descriptors_and_nonconsuming_endpoint_operations_remain_valid() {
        let result = check(
            "fn example()->Result<(),Concurrent::TaskFault> @Async {Concurrent::scope \\mut s -> {let child=s.fork(\\->());for [1,2] as index {let (tx,mut rx)=Channel::bounded<int>(1);let ticket=Channel::detach(mut rx);let local=Channel::attach(ticket);Channel::close(local);Channel::close(tx)};child.join()}}",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let result = check(
            "fn example()->Result<(),Concurrent::TaskFault> @Async {Concurrent::scope \\mut s -> {let child=s.fork(\\->());let (mut tx,mut rx)=Channel::bounded<int>(2);for [1,2] as value {assert((tx !> Channel::send(value)) is Ok());assert((rx !> Channel::recv()) is Ok(_));let local=clone(tx);Channel::close(local)};Channel::close(tx);Channel::close(rx);child.join()}}",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn every_terminal_operation_and_a_possible_next_preserve_linear_consumption() {
        for (setup, operation) in [
            ("", "Channel::close(rx);"),
            (
                "let ticket=Channel::detach(mut rx);",
                "let local=Channel::attach(ticket);Channel::close(local);",
            ),
            ("", "assert(child.join() is Ok());"),
        ] {
            let result = check(&format!(
                "fn example()->Result<(),Concurrent::TaskFault> @Async {{Concurrent::scope \\mut s -> {{let child=s.fork(\\->());let (tx,mut rx)=Channel::bounded<int>(1);{setup}for [0,1] as index {{{operation}}};Channel::close(tx);Ok()}}}}"
            ));
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0603"),
                "{operation}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
        let result = check(
            "fn example(choice:bool)->Result<(),Concurrent::TaskFault> @Async {Concurrent::scope \\mut s -> {let child=s.fork(\\->());let (tx,rx)=Channel::bounded<int>(1);loop {Channel::close(rx);if choice {next}else{last}};Channel::close(tx);child.join()}}",
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0603"),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn repeated_fork_callsite_keeps_each_live_childs_clone_source_borrow() {
        for (completion, accepted) in [
            (
                "assert(first.join() is Ok());assert(second.join() is Ok());Channel::close(tx);",
                true,
            ),
            (
                "assert(first.join() is Ok());Channel::close(tx);assert(second.join() is Ok());",
                false,
            ),
        ] {
            let source = format!(
                "fn example()->Result<(),Concurrent::TaskFault> @Async {{Concurrent::scope \\mut s -> {{let (tx,rx)=Channel::bounded<int>(1);let mut launch=\\->s.fork(\\->{{let local=clone(tx);Channel::close(local)}});let first=launch();let second=launch();{completion}Channel::close(rx);Ok()}}}}"
            );
            let result = check(&source);
            if accepted {
                assert!(
                    result.program.is_some(),
                    "{:?} {:?}",
                    result.diagnostics,
                    result.unsupported
                );
            } else {
                assert!(
                    result
                        .diagnostics
                        .iter()
                        .any(|diagnostic| diagnostic.code == "E0603"),
                    "{:?} {:?}",
                    result.diagnostics,
                    result.unsupported
                );
            }
        }
    }
    #[test]
    fn conditional_range_reuse_cannot_borrow_a_single_iteration_witness() {
        for end in ["2", "limit"] {
            let result = check(&format!(
                "fn example(choice:bool,limit:int)->Result<(),Concurrent::TaskFault> @Async {{Concurrent::scope \\mut s -> {{let child=s.fork(\\->());let (tx,rx)=Channel::bounded<int>(1);let range=\\end:int->0..end;let values=if choice {{range(1)}} else {{range({end})}};for values as index {{Channel::close(rx)}};Channel::close(tx);child.join()}}}}"
            ));
            assert!(
                result.program.is_none(),
                "a possibly repeated range was accepted using another invocation's bound"
            );
        }
        let result = check(
            "fn example()->Result<(),Concurrent::TaskFault> @Async {Concurrent::scope \\mut s -> {let child=s.fork(\\->());let (tx,rx)=Channel::bounded<int>(1);let empty:[]int=[];for empty as index {Channel::close(rx)};Channel::close(rx);Channel::close(tx);child.join()}}",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn joined_child_returns_transport_result() {
        let result = check(
            "fn example()->Result<int,Concurrent::TaskFault> @Concurrent { Concurrent::scope \\mut s -> { let task=s.fork(\\->42); task.join() } }",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn scope_handles_cannot_escape_in_records_or_closures() {
        for output in ["Ok(s)", "Ok(.{handle:s})", "Ok(\\->s)", "Ok(s.fork(\\->1))"] {
            let result = check(&format!(
                "fn example() @Concurrent {{ let result=Concurrent::scope \\mut s -> {{ {output} }}; match result {{ Ok(_) -> {{}}, Err(_) -> {{}} }} }}"
            ));
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0606"),
                "{output}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
    #[test]
    fn child_global_dependencies_are_checked_after_named_calls() {
        let result = check(
            "type Cell={mut count:int}\nlet mut state=Cell.{count:0}\nfn read()->int &{state} {state.count}\nfn example()->Result<int,Concurrent::TaskFault> @Concurrent &{state} { Concurrent::scope \\mut s -> { let task=s.fork(\\->read()); task.join() } }",
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0601"),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn unjoined_business_result_keeps_inspection_duty() {
        let result = check(
            "fn example()->Result<(),Concurrent::TaskFault> @Concurrent { Concurrent::scope \\mut s -> { let task=s.fork(\\-> {let answer:Result<int,str>=Err(\"lost\");answer}); Ok() } }",
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0720"),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn channel_sender_clone_is_child_local_and_borrow_ends_at_join() {
        let result = check(
            "fn example()->Result<int,Concurrent::TaskFault> @Async { Concurrent::scope \\mut s -> { let (tx,mut rx)=Channel::bounded<int>(1); let task=s.fork(\\-> {let mut local=clone(tx); let _=(local !> Channel::send(42)) ?? \\_e -> (); Channel::close(local)}); let value=(rx !> Channel::recv()) ?? \\_e -> 0; task.join()?; Channel::close(tx); Ok(value) } }",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn channel_detached_receiver_can_move_into_child() {
        let result = check(
            "fn example()->Result<int,Concurrent::TaskFault> @Async { Concurrent::scope \\mut s -> { let (mut tx,mut rx)=Channel::bounded<int>(1); let ticket=Channel::detach(mut rx); let task=s.fork(\\-> {let mut local=Channel::attach(ticket); (local !> Channel::recv()) ?? \\_e -> 0}); let _=(tx !> Channel::send(42)) ?? \\_e -> (); task.join() } }",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn channel_consumption_and_borrow_reject_aliases() {
        for operation in [
            "let ticket=Channel::detach(mut rx); let _=(rx !> Channel::recv()) ?? \\_e -> 0;",
            "let ticket=Channel::detach(mut rx); let first=Channel::attach(ticket); let second=Channel::attach(ticket);",
            "let task=s.fork(\\->{let copy=clone(tx); Channel::close(copy)}); Channel::close(tx);",
            "let task=s.fork(\\-> Channel::close(tx));",
        ] {
            let result = check(&format!(
                "fn example()->Result<(),Concurrent::TaskFault> @Async {{ Concurrent::scope \\mut s -> {{ let (tx,mut rx)=Channel::bounded<int>(1); {operation} Ok() }} }}"
            ));
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0603"),
                "{operation}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
    #[test]
    fn resource_identity_survives_named_fork_and_join_helpers() {
        let result = check(
            "fn start(mut s:Concurrent::Scope)->Concurrent::Task<int> @Concurrent &mut {s.fork(\\->3)}\nfn finish(task:Concurrent::Task<int>)->Result<int,Concurrent::TaskFault> @Concurrent {task.join()}\nfn example()->Result<int,Concurrent::TaskFault> @Concurrent {Concurrent::scope \\mut s -> {let task=start(mut s);finish(task)}}",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn wrapped_sender_borrow_keeps_the_owner_blocked_until_join() {
        for (closing, accepted) in [
            ("task.join()?; Channel::close(tx);", true),
            ("Channel::close(tx); task.join()?;", false),
        ] {
            let result = check(&format!(
                "fn example()->Result<(),Concurrent::TaskFault> @Async {{Concurrent::scope \\mut s -> {{let (tx,rx)=Channel::bounded<int>(1); let wrapper=.{{sender:tx}}; let task=s.fork(\\->{{let own=clone(wrapper.sender);Channel::close(own)}}); {closing} Channel::close(rx); Ok()}}}}"
            ));
            if accepted {
                assert!(
                    result.program.is_some(),
                    "{:?} {:?}",
                    result.diagnostics,
                    result.unsupported
                );
            } else {
                assert!(
                    result
                        .diagnostics
                        .iter()
                        .any(|diagnostic| diagnostic.code == "E0603"),
                    "{:?} {:?}",
                    result.diagnostics,
                    result.unsupported
                );
            }
        }
    }
    #[test]
    fn message_results_keep_their_inner_inspection_duty() {
        for (receive, accepted) in [
            (
                "match (rx !> Channel::recv()) {Ok(business)->assert(business is Err(\"domain\")),Err(_)->()}",
                true,
            ),
            (
                "match (rx !> Channel::recv()) {Ok(_)->(),Err(_)->()}",
                false,
            ),
            ("Channel::close(rx)", false),
        ] {
            let source = format!(
                "fn example()->Result<(),Concurrent::TaskFault> @Async {{Concurrent::scope \\mut s -> {{let task=s.fork(\\->());let (mut tx,mut rx)=Channel::bounded<Result<int,str>>(1);let business:Result<int,str>=Err(\"domain\");assert((tx !> Channel::send(business)) is Ok());{receive};task.join()?;Ok()}}}}"
            );
            let result = check(&source);
            if accepted {
                assert!(
                    result.program.is_some(),
                    "{:?} {:?}",
                    result.diagnostics,
                    result.unsupported
                );
            } else {
                assert!(
                    result
                        .diagnostics
                        .iter()
                        .any(|diagnostic| diagnostic.code == "E0720"),
                    "{:?} {:?}",
                    result.diagnostics,
                    result.unsupported
                );
            }
        }
    }
    #[test]
    fn conditional_join_and_detach_do_not_restore_linear_authority() {
        for (operation, code) in [
            (
                "let task=s.fork(\\->{let x:Result<int,str>=Err(\"lost\");x}); if choice {let nested=task.join();match nested {Ok(x)->assert(x is Err(_)),Err(_)->()}};",
                "E0720",
            ),
            (
                "let task=s.fork(\\->());let (tx,mut rx)=Channel::bounded<int>(1);if choice {let ticket=Channel::detach(mut rx);let local=Channel::attach(ticket);Channel::close(local)};Channel::close(rx);Channel::close(tx);assert(task.join() is Ok());",
                "E0603",
            ),
        ] {
            let result = check(&format!(
                "fn example(choice:bool)->Result<(),Concurrent::TaskFault> @Async {{Concurrent::scope \\mut s -> {{{operation}Ok()}}}}"
            ));
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == code),
                "{operation}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
    #[test]
    fn child_effect_requires_local_handler_even_under_ambient_handler() {
        let result = check(
            "eff Read { get()->int }\nfn example()->Result<int,Concurrent::TaskFault> @Concurrent { with Read::get()->resume 1; Concurrent::scope \\mut s -> {let task=s.fork(\\->Read::get()); task.join()} }",
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0615"),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let result = check(
            "eff Read { get()->int }\nfn example()->Result<int,Concurrent::TaskFault> @Concurrent { Concurrent::scope \\mut s -> {let task=s.fork(\\->{with Read::get()->resume 1; Read::get()}); task.join()} }",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn latent_module_dependencies_cannot_hide_in_transferred_callbacks() {
        let result = check(
            "type Cell={mut count:int}\nlet mut state=Cell.{count:0}\nfn read()->int &{state} {state.count}\nfn example() @Concurrent {let result=Concurrent::scope \\mut s -> {let task=s.fork(\\-> (\\->read()));task.join()};match result {Ok(_)->(),Err(_)->()}}",
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0601"),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let result = check(
            "type Cell={mut count:int}\nlet STATE=Cell.{count:0}\nfn read()->int &{STATE} {STATE.count}\nfn example() @Concurrent &{STATE} {let result=Concurrent::scope \\mut s -> {let task=s.fork(\\-> (\\->read()));task.join()};match result {Ok(callback)->assert(callback()==0),Err(_)->()}}",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn returning_a_detached_ticket_does_not_revive_parent_aliases() {
        for (selected, accepted) in [("returned", true), ("ticket", false)] {
            let result = check(&format!(
                "fn example()->Result<(),Concurrent::TaskFault> @Async {{Concurrent::scope \\mut s -> {{let (tx,mut rx)=Channel::bounded<int>(1);let ticket=Channel::detach(mut rx);let task=s.fork(\\->ticket);let returned=task.join()?;let local=Channel::attach({selected});Channel::close(local);Channel::close(tx);Ok()}}}}"
            ));
            if accepted {
                assert!(
                    result.program.is_some(),
                    "{:?} {:?}",
                    result.diagnostics,
                    result.unsupported
                );
            } else {
                assert!(
                    result
                        .diagnostics
                        .iter()
                        .any(|diagnostic| diagnostic.code == "E0603"),
                    "{:?} {:?}",
                    result.diagnostics,
                    result.unsupported
                );
            }
        }
    }
}
