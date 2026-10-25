use super::*;
use crate::sema::evaluated::SourceRef;
use crate::sema::source_types::SourceSchema;
use crate::sema::summary::InvocationSummary;
use std::sync::Arc;

/// Body checks refer to the same retained record later consumed by replay.
/// Primitive transfers have no entered source body; their contract is separate.
#[derive(Clone)]
pub(super) enum CompletedInvocation {
    Recorded(ril_compiler_core::ids::InvocationSummaryId),
    Intrinsic(Box<InvocationSummary>),
}

/// A temporary path through a real receiving header. Alias instantiation and
/// standard interface elaboration never create another original Source root.
pub(super) struct SignatureSource<'a> {
    pub header: &'a TypeExpr,
    pub environment: crate::sema::context::FrozenEnvironment,
    pub path: Vec<crate::sema::source_types::SourcePath>,
    pub schema: Option<SourceSchema>,
}

impl<'a> SignatureSource<'a> {
    pub(super) fn receiving(target: &'a crate::sema::source_reception::Target) -> Option<Self> {
        let syntax = target.syntax.as_deref()?;
        Some(Self {
            header: target
                .source
                .as_ref()
                .map_or(syntax, |source| &source.header),
            environment: target.source.as_ref().map_or_else(
                || target.environment.clone(),
                |source| source.environment.clone(),
            ),
            path: target
                .source
                .as_ref()
                .map_or_else(Vec::new, |source| source.path.clone()),
            schema: target.schema.clone(),
        })
    }

    fn project(
        &self,
        step: crate::sema::source_types::SourcePath,
    ) -> Result<Self, crate::sema::source_types::SourceTypesError> {
        let mut work = crate::sema::source_types::WorkLimit::new(16384);
        work.charge(self.path.len() + 1)?;
        for step in self.path.iter().chain(std::iter::once(&step)) {
            if let crate::sema::source_types::SourcePath::Field(label) = step {
                work.text(label)?;
            }
        }
        let mut path = self.path.clone();
        path.push(step.clone());
        Ok(Self {
            header: self.header,
            environment: self.environment.clone(),
            path,
            schema: self
                .schema
                .as_ref()
                .map(|schema| schema.project_steps(std::slice::from_ref(&step), &mut work))
                .transpose()?,
        })
    }
}

/// The comma makes `closure` a contextual group header. Without it the
/// same spelling is an ordinary module binding, even before name resolution.
pub(crate) struct StateGroup<'a> {
    pub capture_owner: Option<&'a str>,
    parts: std::str::Split<'a, char>,
}

pub(crate) struct StateItem<'a> {
    pub mode: Mode,
    pub name: &'a str,
}

impl<'a> StateGroup<'a> {
    pub fn items(self) -> impl Iterator<Item = StateItem<'a>> {
        self.parts
            .map(str::trim)
            .filter(|item| !item.is_empty())
            .map(|item| {
                let (mode, name) = if let Some(name) = item.strip_prefix("^mut ") {
                    (Mode::Retain, name.trim())
                } else if let Some(name) = item.strip_prefix("mut ") {
                    (Mode::Write, name.trim())
                } else {
                    (Mode::Read, item)
                };
                StateItem { mode, name }
            })
    }
}

pub(crate) fn state_group(text: &str) -> Option<StateGroup<'_>> {
    let inner = text.strip_prefix("&{")?.strip_suffix('}')?;
    let mut parts = inner.split(',');
    let first = parts.next()?.trim();
    let capture_owner = if inner.contains(',') {
        first
            .strip_prefix("closure")
            .filter(|rest| rest.is_empty() || rest.starts_with(char::is_whitespace))
            .map(str::trim)
    } else {
        None
    };
    if capture_owner.is_none() {
        parts = inner.split(',');
    }
    Some(StateGroup {
        capture_owner,
        parts,
    })
}

/// Coverage of the actual latent summaries, separate from satisfaction of a
/// particular bound. Complete never erases diagnostics or unresolved rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BoundProbe {
    Open,
    Complete,
    Unresolved,
}

pub(super) struct CanonicalBuiltinSummary {
    pub effects: BTreeSet<String>,
    pub concrete_effects: BTreeSet<String>,
    pub written_formals: BTreeSet<u32>,
    pub captures: BTreeSet<BindingId>,
}

#[derive(Clone)]
pub(super) struct ContractEnvironment {
    owner: ScopeId,
    scope: u32,
    typing_environment: crate::sema::context::FrozenEnvironment,
}
impl Checker {
    pub(super) fn ascribe_received_signature(
        &mut self,
        value: &mut Value,
        target: &crate::sema::source_reception::Target,
    ) {
        if let Some(source) = SignatureSource::receiving(target) {
            let syntax = target
                .source
                .as_ref()
                .filter(|source| source.path.is_empty())
                .map(|source| source.header.as_ref())
                .unwrap_or_else(|| {
                    target
                        .syntax
                        .as_deref()
                        .expect("receiving signature syntax")
                });
            self.with_typing_environment(&target.environment, |checker| {
                checker.ascribe_signature_from(value, syntax, &source);
            });
        }
    }

    pub(super) fn callable_signature(&self, parameters: Vec<Parameter>) -> Arc<CallableSignature> {
        Arc::new(CallableSignature {
            parameters,
            generics: vec![],
            environment: self.capture_typing_environment(),
        })
    }

    pub(super) fn completed_summary(&self) -> Option<&InvocationSummary> {
        match self.completed_invocation.as_ref()? {
            CompletedInvocation::Recorded(id) => self.invocations.get(id.0 as usize),
            CompletedInvocation::Intrinsic(summary) => Some(summary),
        }
    }

    pub(super) fn complete_intrinsic_summary(&mut self, frame: &Frame) {
        self.completed_invocation = Some(CompletedInvocation::Intrinsic(Box::new(
            InvocationSummary {
                activation: Some(frame.owner),
                ..InvocationSummary::from_obligations(&frame.obligations)
            },
        )));
    }

    pub(super) fn retain_invocation_summary(
        &mut self,
        summary: InvocationSummary,
    ) -> ril_compiler_core::ids::InvocationSummaryId {
        let id = ril_compiler_core::ids::InvocationSummaryId(self.invocations.len() as u32);
        if let Some(context) = summary.context {
            match context.owner {
                Some(CallableOwner::Function(_)) => {
                    if let Some(call) = context
                        .invocation
                        .and_then(|id| self.copy_invocations.get_mut(id.0 as usize))
                    {
                        call.summary = Some(id);
                    }
                }
                Some(CallableOwner::Lambda(_)) => {
                    if let Some(call) = context
                        .closure_invocation
                        .and_then(|id| self.closure_invocations.get_mut(id.0 as usize))
                    {
                        call.summary = Some(id);
                    }
                }
                _ => {}
            }
        }
        self.invocations.push(summary);
        id
    }

    pub(super) fn lambda_contract(&self, id: usize) -> Option<&LambdaContract> {
        self.closures
            .get(id)
            .map(|closure| closure.contract.as_ref())
    }
    /// Execute a primitive's semantic transfer in an isolated latent frame.
    /// This reports its actual obligations; it does not make a caller's row
    /// true or manufacture a source witness from the primitive's runtime Ty.
    pub(super) fn probe_canonical_builtin_summary(
        &mut self,
        value: &Value,
        header: &TypeExpr,
        span: Span,
    ) -> Option<CanonicalBuiltinSummary> {
        let [Callable::Builtin(name)] = value.callables.as_slice() else {
            return None;
        };
        if !matches!(
            name.as_str(),
            "File::read_chunk" | "File::write" | "Process::wait" | "Process::terminate"
        ) && crate::sema::source_types::builtins::BuiltinId::lookup(name).is_none()
            || self.operations.contains_key(name)
        {
            return None;
        }
        let TypeKind::Callable { parameters, .. } = &header.kind else {
            return None;
        };
        if value
            .signature
            .as_ref()
            .map(|signature| &signature.parameters)
            != Some(parameters)
        {
            return None;
        }
        let preview = self.snapshot_flow();
        let handlers = std::mem::take(&mut self.active_handlers);
        let mut context = self.frame(Env::new(), true);
        let summary = (|| {
            let mut arguments = Vec::new();
            let mut formal_roots = Vec::new();
            for (index, parameter) in parameters.iter().enumerate() {
                let ty = self.ty(parameter.ty.as_ref()?);
                let mut argument =
                    self.formal_value(ty, index as u32, parameter.span, &mut BTreeSet::new());
                if parameter.mode != ParameterMode::Read {
                    argument.permission = Permission::Write;
                }
                let binding = self.bind_name(
                    &format!("ril__primitive_formal_{index}"),
                    if parameter.mode == ParameterMode::Read {
                        BindingMode::Let
                    } else {
                        BindingMode::LetMut
                    },
                    argument,
                    parameter.span,
                    &mut context,
                    true,
                );
                arguments.push((
                    parameter.mode,
                    self.bindings[binding].value.clone(),
                    parameter.span,
                ));
                formal_roots.push(self.bindings[binding].value.origins.nodes.clone());
            }
            let diagnostics = self.diagnostics.len();
            let unsupported = self.unsupported.len();
            self.transfer_builtin(name, arguments, span, &mut context);
            if self.unsupported.len() != unsupported
                || self.diagnostics[diagnostics..]
                    .iter()
                    .any(|diagnostic| diagnostic.severity == Severity::Error)
            {
                return None;
            }
            let obligations = &context.obligations;
            if obligations.symbolic
                || obligations.capture
                || obligations.handler_environment
                || obligations.retention
            {
                return None;
            }
            let captures = obligations
                .named
                .keys()
                .filter(|binding| self.bindings[**binding].owner != context.owner)
                .copied()
                .collect();
            let mut written_formals = BTreeSet::new();
            for access in obligations
                .accesses
                .iter()
                .filter(|access| access.mode != Mode::Read)
            {
                if access.origins.nodes.is_empty() {
                    return None;
                }
                for node in &access.origins.nodes {
                    let mut slots = formal_roots
                        .iter()
                        .enumerate()
                        .filter_map(|(slot, roots)| roots.contains(node).then_some(slot as u32));
                    let slot = slots.next()?;
                    if slots.next().is_some() {
                        return None;
                    }
                    written_formals.insert(slot);
                }
            }
            Some(CanonicalBuiltinSummary {
                effects: obligations.effects.clone(),
                concrete_effects: obligations.concrete_effects.clone(),
                written_formals,
                captures,
            })
        })();
        self.restore_definition_state(&preview);
        self.active_handlers = handlers;
        summary
    }

    /// Keep contextual result contracts on the particular callable value. A
    /// closure definition can flow through several differently sealed values.
    pub(super) fn ascribe_callable_return(
        &mut self,
        value: &mut Value,
        syntax: &TypeExpr,
        origin: &SignatureSource<'_>,
    ) {
        fn result_syntax(
            checker: &Checker,
            syntax: &TypeExpr,
            seen: &mut BTreeSet<String>,
        ) -> Option<TypeExpr> {
            match &syntax.kind {
                TypeKind::Callable { result, .. } => {
                    Some(result.as_deref().cloned().unwrap_or_else(|| TypeExpr {
                        hir_id: None,
                        text: "()".into(),
                        kind: TypeKind::Tuple(vec![]),
                        span: syntax.span,
                    }))
                }
                TypeKind::Name { path, arguments } if arguments.is_empty() => {
                    let name = path.join("::");
                    if !seen.insert(name.clone()) {
                        return None;
                    }
                    let declaration = checker.types.get(&name)?;
                    if declaration.nominal
                        || (declaration.opaque && declaration.span.file != syntax.span.file)
                    {
                        return None;
                    }
                    result_syntax(checker, declaration.value.as_ref()?, seen)
                }
                _ => None,
            }
        }
        let Some(result) = result_syntax(self, syntax, &mut BTreeSet::new()) else {
            return;
        };
        let environment = self.capture_typing_environment();
        let mut work = crate::sema::source_types::WorkLimit::new(32768);
        let source = (|| {
            let callable = self.signature_type_schema(origin, &mut work)?;
            let (_, result) = callable
                .callable_parts(&mut work)?
                .ok_or(crate::sema::source_types::SourceTypesError::MissingProjection)?;
            SourceRef::intern(
                &result,
                environment.clone(),
                self.type_source.storage.live_types_mut(),
                &mut work,
            )
        })();
        let source = source.ok();
        if !self.application_effect.admit(32768 - work.remaining()) {
            self.unsupported(syntax.span, "callable return type exceeded its work bound");
        }
        let bound = CallableReturnBound {
            raw: false,
            predecessors: vec![],
            target: self.ty(&result),
            source,
            syntax: result,
            span: syntax.span,
            callables: value.callables.clone(),
            typing_environment: environment,
        };
        let same_stage = |previous: &Arc<CallableReturnBound>| {
            !previous.raw
                && previous.target == bound.target
                && previous.syntax == bound.syntax
                && previous.span == bound.span
                && previous.callables == bound.callables
                && previous.typing_environment == bound.typing_environment
        };
        if !value.callable_returns.is_empty() && value.callable_returns.iter().all(same_stage) {
            return;
        }
        let mut bound = bound;
        bound.predecessors = std::mem::take(&mut value.callable_returns);
        value.callable_returns.push(Arc::new(bound));
    }

    pub(super) fn apply_callable_returns(
        &mut self,
        callee: &Value,
        callable: &Callable,
        result: Value,
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        struct Evaluation<'a> {
            callable: &'a Callable,
            actual: &'a Value,
            before: &'a super::flow::FlowSnapshot,
            frame: &'a Frame,
            span: Span,
            cache: BTreeMap<usize, (Value, super::flow::FlowSnapshot)>,
        }
        fn evaluate(
            checker: &mut Checker,
            bound: &Arc<CallableReturnBound>,
            depth: usize,
            context: &mut Evaluation<'_>,
        ) -> Option<(Value, super::flow::FlowSnapshot)> {
            let key = Arc::as_ptr(bound) as usize;
            if let Some(cached) = context.cache.get(&key) {
                return Some(cached.clone());
            }
            if depth > 64 || context.cache.len() > 256 {
                return None;
            }
            if bound.raw {
                let output = (context.actual.clone(), context.before.clone());
                context.cache.insert(key, output.clone());
                return Some(output);
            }
            let mut predecessors = Vec::new();
            let callable = context.callable;
            for predecessor in bound
                .predecessors
                .iter()
                .filter(|head| head.callables.contains(callable))
            {
                predecessors.push(evaluate(checker, predecessor, depth + 1, context)?);
            }
            if predecessors.is_empty() {
                predecessors.push((context.actual.clone(), context.before.clone()));
            }
            let mut combined = None;
            for (mut alternative, state) in predecessors {
                checker.restore_preview(&state);
                checker.apply_callable_return_stage(bound, &mut alternative, context.frame);
                if let Some((previous, state)) = combined {
                    alternative = checker.branch_flow(
                        context.before,
                        &state,
                        &previous,
                        &alternative,
                        context.span,
                    );
                }
                combined = Some((alternative, checker.snapshot_flow()));
            }
            let output = combined.unwrap();
            context.cache.insert(key, output.clone());
            Some(output)
        }
        if callee.callable_returns.is_empty() || result.ty == Ty::Never {
            return result;
        }
        let previous_typing = self.capture_typing_environment();
        let before = self.snapshot_flow();
        let mut combined = None;
        let mut context = Evaluation {
            callable,
            actual: &result,
            before: &before,
            frame,
            span,
            cache: BTreeMap::new(),
        };
        for head in callee
            .callable_returns
            .iter()
            .filter(|head| head.callables.contains(callable))
        {
            match evaluate(self, head, 0, &mut context) {
                Some((mut alternative, state)) => {
                    self.restore_preview(&state);
                    if let Some((previous, state)) = combined {
                        alternative =
                            self.branch_flow(&before, &state, &previous, &alternative, span);
                    }
                    combined = Some((alternative, self.snapshot_flow()));
                }
                None => {
                    self.restore_preview(&before);
                    self.unsupported(
                        span,
                        "callable return contract graph resource budget exhausted",
                    );
                    combined = None;
                    break;
                }
            }
        }
        self.restore_typing_environment(previous_typing);
        combined.map(|(value, _)| value).unwrap_or(result)
    }

    fn apply_callable_return_stage(
        &mut self,
        bound: &CallableReturnBound,
        alternative: &mut Value,
        frame: &Frame,
    ) {
        self.restore_typing_environment(bound.typing_environment.clone());
        // Contextual inference rewrites this value's checked target while the
        // retained source syntax still names its declaration's binders. Carry
        // that already selected identity into nested return-contract syntax.
        let syntax_target = self.ty(&bound.syntax);
        let mut syntax_names = BTreeSet::new();
        syntax_target.generic_names(&mut syntax_names);
        let binders = bound
            .typing_environment
            .generic_context
            .values()
            .cloned()
            .chain(
                syntax_names
                    .into_iter()
                    .filter(|name| self.inference_metas.contains(name)),
            )
            .collect();
        let mut selected = BTreeMap::new();
        if super::types::unify_call_types(&syntax_target, &bound.target, &binders, &mut selected) {
            self.type_source
                .environment
                .generic_substitutions
                .extend(selected);
        }
        let mut origin = self.signature_source(&bound.syntax);
        if let Some(source) = bound.source {
            match self.type_source.storage.live_types().view_schema(
                source.view,
                source.original,
                &mut crate::sema::source_types::WorkLimit::new(16384),
            ) {
                Ok((schema, _)) => origin.schema = Some(schema),
                Err(error) => self.unsupported(
                    bound.span,
                    format!("callable return type is unavailable: {error}"),
                ),
            }
        }
        self.ascribe_signature_from(alternative, &bound.syntax, &origin);
        self.require_type(alternative, &bound.target, bound.span);
        let mut shape_frame = frame.clone();
        self.check_storage_shape(alternative, &bound.syntax, &mut shape_frame);
        // Contracts only restrict actual provenance. Unknown results cannot
        // gain a known graph or writable authority through a declaration.
        if alternative.ty == Ty::Unknown && bound.target != Ty::Unknown {
            self.unsupported(
                bound.span,
                "a callable result contract requires a known result shape",
            );
        } else {
            if self.formal_is_immutable(&bound.target) {
                alternative.permission = Permission::Read;
                alternative.construction = false;
            }
            alternative.ty = bound.target.clone();
        }
    }

    pub(super) fn set_contract_environment(&mut self, environment: &Env) {
        self.type_source.environment.contract_bindings = environment.clone();
    }
    pub(super) fn register_type_contract_environments(
        &mut self,
        declaration: &TypeDeclaration,
        frame: &Frame,
    ) {
        fn visit(ty: &TypeExpr, sources: &mut Vec<ril_compiler_core::ids::TypeExprId>) {
            match &ty.kind {
                TypeKind::Callable {
                    parameters,
                    result,
                    annotations,
                } => {
                    if !annotations.is_empty() {
                        sources.extend(ty.hir_id);
                    }
                    for parameter in parameters {
                        if let Some(ty) = &parameter.ty {
                            visit(ty, sources);
                        }
                    }
                    if let Some(result) = result {
                        visit(result, sources);
                    }
                }
                TypeKind::Tuple(items) => {
                    for item in items {
                        visit(item, sources);
                    }
                }
                TypeKind::Record { fields, row } => {
                    for field in fields {
                        visit(&field.ty, sources);
                    }
                    if let Some(row) = row {
                        visit(row, sources);
                    }
                }
                TypeKind::Name { arguments, .. } => {
                    for argument in arguments {
                        visit(argument, sources);
                    }
                }
                TypeKind::Array { element, .. } | TypeKind::Optional(element) => {
                    visit(element, sources)
                }
                TypeKind::Map { key, value } => {
                    visit(key, sources);
                    visit(value, sources);
                }
                _ => {}
            }
        }
        let mut sources = Vec::new();
        if let Some(value) = &declaration.value {
            visit(value, &mut sources);
        }
        for source in sources {
            let typing_environment = self.capture_typing_environment_with_bindings(&frame.env);
            self.type_contract_environments.insert(
                source,
                ContractEnvironment {
                    owner: frame.owner,
                    scope: self.block_boundaries.last().copied().unwrap_or(u32::MAX),
                    typing_environment,
                },
            );
        }
    }
    pub(super) fn update_type_contract_environments(&mut self, binding: BindingId) {
        let info = &self.bindings[binding];
        for environment in self.type_contract_environments.values_mut() {
            if environment.owner == info.owner && environment.scope == info.lexical_scope {
                let mut bindings = environment.typing_environment.contract_bindings().clone();
                bindings.insert(info.name.clone(), binding);
                environment.typing_environment = environment
                    .typing_environment
                    .with_contract_bindings(bindings);
            }
        }
    }
    pub(super) fn validate_empty_callable_rows(
        &mut self,
        ty: &Ty,
        annotations: &[Annotation],
        span: Span,
    ) {
        fn contains(checker: &Checker, ty: &Ty, seen: &mut BTreeSet<String>) -> bool {
            if !seen.insert(format!("{ty:?}")) {
                return false;
            }
            match checker.expanded(ty, &mut BTreeSet::new()) {
                Ty::Callable(..) => true,
                Ty::Tuple(items) => items.iter().any(|ty| contains(checker, ty, seen)),
                Ty::Record(fields) => fields.values().any(|(_, ty)| contains(checker, ty, seen)),
                Ty::Array(inner) | Ty::Set(inner) | Ty::Optional(inner) | Ty::Immutable(inner) => {
                    contains(checker, &inner, seen)
                }
                Ty::Map(a, b) | Ty::Result(a, b) => {
                    contains(checker, &a, seen) || contains(checker, &b, seen)
                }
                _ => false,
            }
        }
        if !annotations
            .iter()
            .any(|annotation| matches!(annotation.text.trim(), "@{}" | "&{}"))
        {
            return;
        }
        let higher_order = match self.expanded(ty, &mut BTreeSet::new()) {
            Ty::Callable(parameters, result) => {
                parameters
                    .iter()
                    .any(|ty| contains(self, ty, &mut BTreeSet::new()))
                    || contains(self, &result, &mut BTreeSet::new())
            }
            _ => false,
        };
        if !higher_order {
            self.error(
                "E0542",
                span,
                "empty rows require a higher-order signature",
                [],
            );
        }
    }
    pub(super) fn signature_source<'a>(&mut self, syntax: &'a TypeExpr) -> SignatureSource<'a> {
        let environment = self
            .callable_type_source(syntax)
            .and_then(|id| self.type_contract_environments.get(&id))
            .map(|source| source.typing_environment.clone())
            .unwrap_or_else(|| self.capture_typing_environment());
        let schema = if syntax.hir_id.is_none() {
            self.source_type_from_syntax(syntax).and_then(|source| {
                let key = crate::static_eval::effects::bounded_argument_key(
                    &source.syntax,
                    &BTreeMap::new(),
                )?;
                SourceSchema::import(
                    &key,
                    None,
                    &mut crate::sema::source_types::WorkLimit::new(16384),
                )
                .ok()
            })
        } else {
            None
        };
        SignatureSource {
            header: syntax,
            environment,
            path: Vec::new(),
            schema,
        }
    }

    fn signature_type_schema(
        &self,
        origin: &SignatureSource<'_>,
        work: &mut crate::sema::source_types::WorkLimit,
    ) -> Result<SourceSchema, crate::sema::source_types::SourceTypesError> {
        match &origin.schema {
            Some(schema) => Ok(schema.clone()),
            None => self
                .original_header_source_schema(origin.header, work)?
                .project_steps(&origin.path, work),
        }
    }

    pub(super) fn ascribe_callable_bounds_from(
        &mut self,
        value: &mut Value,
        syntax: &TypeExpr,
        annotations: &[Annotation],
        origin: &SignatureSource<'_>,
    ) -> BoundProbe {
        let contextual_closure = value.callables.iter().any(|callable| {
            matches!(callable, Callable::Closure(id) if !self.checked_closures.contains(id))
        });
        if annotations.is_empty() && !contextual_closure {
            return BoundProbe::Open;
        }
        self.validate_empty_callable_rows(&value.ty, annotations, syntax.span);
        let source = self.callable_type_source(syntax);
        let typing_environment = origin.environment.clone();
        let bound = CallableBound {
            annotations: annotations.to_vec(),
            source: source.map(ril_compiler_core::ids::CallableContractSource::Type),
            typing_environment,
            span: syntax.span,
        };
        if !annotations.is_empty() && !value.callable_bounds.contains(&bound) {
            value.callable_bounds.push(bound.clone());
        }
        let key = (
            syntax.span.file.0,
            syntax.span.start,
            syntax.span.end,
            value.cause.0,
        );
        if !self.probing_contracts.insert(key) {
            return BoundProbe::Unresolved;
        }
        if let [Callable::Builtin(name)] = value.callables.as_slice()
            && let Some(id) = ril_compiler_core::builtin_calls::GenericBuiltin::lookup(name)
        {
            let target = self.freeze_source_receiving_target(syntax);
            let instance = target
                .schema
                .as_ref()
                .ok_or(crate::sema::source_types::SourceTypesError::Unresolved)
                .and_then(|source| {
                    source.instantiate_builtin(
                        id,
                        &mut crate::sema::source_types::WorkLimit::new(16384),
                    )
                });
            let result = match instance {
                Ok(Some(instance)) => {
                    // A primitive declaration has a closed latent contract.
                    // Checking that contract creates no hypothetical heap
                    // writes, loans, fake call or borrowed application token.
                    let obligations = InvocationSummary {
                        parameter_write: instance.parameter_write,
                        retention: instance.retention,
                        ..Default::default()
                    };
                    self.check_contract(
                        &bound,
                        ScopeId(0),
                        &obligations,
                        syntax.span,
                        &BTreeSet::new(),
                    );
                    BoundProbe::Complete
                }
                Ok(None) => {
                    self.error(
                        "E0301",
                        syntax.span,
                        "primitive callable bound has no matching full Source instance",
                        [value.cause],
                    );
                    BoundProbe::Unresolved
                }
                Err(_) => {
                    self.unsupported(
                        syntax.span,
                        "primitive callable bound lacks its complete frozen Source instance",
                    );
                    BoundProbe::Unresolved
                }
            };
            self.probing_contracts.remove(&key);
            return result;
        }
        let Some(signature) = value.signature.clone() else {
            self.unsupported(
                syntax.span,
                "callable row bounds require a checked parameter signature",
            );
            self.probing_contracts.remove(&key);
            return BoundProbe::Unresolved;
        };
        let parameters = &signature.parameters;
        let mut source_work = crate::sema::source_types::WorkLimit::new(32768);
        let probe_type = self.with_typing_environment(&signature.environment, |checker| {
            let callable = checker.signature_type_schema(origin, &mut source_work)?;
            checker.selected_input_schema(callable, signature.environment.clone(), &mut source_work)
        });
        let probe_type = probe_type.and_then(|(schema, environment)| {
            let formals = schema.callable_parameters(&mut source_work)?;
            if formals.len() != parameters.len()
                || formals
                    .iter()
                    .zip(parameters)
                    .any(|((mode, _), parameter)| *mode != parameter.mode)
            {
                return Err(crate::sema::source_types::SourceTypesError::Unresolved);
            }
            Ok((schema, environment))
        });
        let admitted = self
            .application_effect
            .admit(32768 - source_work.remaining() + parameters.len() + 1);
        let (schema, environment) = match probe_type {
            Ok(probe_type) if admitted => probe_type,
            result => {
                self.unsupported(
                    syntax.span,
                    format!("callable signature type is incomplete: {result:?}"),
                );
                self.probing_contracts.remove(&key);
                return BoundProbe::Unresolved;
            }
        };
        let probe_source = Arc::new(crate::sema::application_effect::SignatureProbeSource {
            schema: Arc::new(schema),
            environment,
        });
        // Check fixed body obligations at ascription even when the value is
        // never called. Symbolic callback dependence is constrained again at
        // each invocation with the actual callback values.
        let preview = self.snapshot_flow();
        let handlers = std::mem::take(&mut self.active_handlers);
        let previous_completed = self.completed_invocation.clone();
        let mut context = self.frame(bound.typing_environment.contract_bindings().clone(), true);
        context.input_environment = Some(signature.environment.clone());
        let mut arguments = Vec::new();
        let previous_environment = self.enter_typing_environment(&signature.environment);
        for (index, parameter) in parameters.iter().enumerate() {
            let ty = parameter
                .ty
                .as_ref()
                .map(|ty| self.ty(ty))
                .unwrap_or(Ty::Unknown);
            let mut argument =
                self.formal_value(ty, index as u32, parameter.span, &mut BTreeSet::new());
            if parameter.mode != ParameterMode::Read && !self.formal_is_immutable(&argument.ty) {
                argument.permission = Permission::Write;
            }
            if let Some(ty) = &parameter.ty {
                self.ascribe_signature(&mut argument, ty);
                self.promise_array_shape(&argument, ty, &mut context);
            }
            let binding = self.bind_name(
                &format!("ril__contract_argument_{index}"),
                if parameter.mode == ParameterMode::Read {
                    BindingMode::Let
                } else {
                    BindingMode::LetMut
                },
                argument,
                parameter.span,
                &mut context,
                true,
            );
            let argument = self.bindings[binding].value.clone();
            arguments.push((parameter.mode, argument, parameter.span));
        }
        self.restore_typing_environment(previous_environment);
        let invocation_state = self.snapshot_flow();
        let mut complete = !value.callables.is_empty();
        for callable in value.callables.clone() {
            if annotations.is_empty()
                && !matches!(callable, Callable::Closure(id) if !self.checked_closures.contains(&id))
            {
                continue;
            }
            self.restore_preview(&invocation_state);
            self.widen_callable_environment(&callable);
            self.completed_invocation = None;
            let captures = self.contract_captures(&callable);
            match callable {
                Callable::Named(id, instance) => {
                    self.invoke_named_generated_from(
                        id,
                        instance,
                        arguments.clone(),
                        syntax.span,
                        Some(&mut context),
                        crate::sema::application_effect::EntryOrigin::SignatureProbe(
                            probe_source.clone(),
                        ),
                    );
                }
                Callable::Closure(id) => {
                    let returned = self.invoke_closure_signature(
                        id,
                        arguments.clone(),
                        syntax.span,
                        &mut context,
                        probe_source.clone(),
                    );
                    self.with_typing_environment(&signature.environment, |checker| {
                        if let Ty::Callable(_, expected) = checker.ty(syntax)
                            && !checker.compatible_at(&returned.ty, &expected, syntax.span.file)
                        {
                            checker.error(
                                "E0301",
                                syntax.span,
                                "anonymous function result does not fit callable context",
                                [returned.cause],
                            );
                        }
                    });
                }
                Callable::Symbolic(..) => {
                    complete = false;
                    continue;
                }
                Callable::Builtin(ref name)
                    if standard::builtin_callable_signature(name, syntax.span).is_some()
                        || (standard::storage_callable(name) && value.signature.is_some()) =>
                {
                    if self
                        .standard_typed_builtin(name, &arguments, syntax.span, &mut context)
                        .is_none()
                    {
                        self.builtin(name, arguments.clone(), syntax.span, &mut context);
                    }
                    self.complete_intrinsic_summary(&context);
                }
                _ => {
                    self.unsupported(syntax.span,"bounded builtin or constructor needs a complete latent invocation contract");
                    complete = false;
                    continue;
                }
            }
            if let Some(obligations) = self.completed_summary().cloned()
                && let Some(owner) = obligations.activation
            {
                self.check_contract(&bound, owner, &obligations, syntax.span, &captures);
            } else {
                complete = false;
                self.unsupported(
                    syntax.span,
                    "recursive callable bound requires a complete invocation summary",
                );
            }
        }
        self.restore_definition_state(&preview);
        self.active_handlers = handlers;
        self.completed_invocation = previous_completed;
        self.probing_contracts.remove(&key);
        if complete {
            BoundProbe::Complete
        } else {
            BoundProbe::Unresolved
        }
    }

    fn callable_type_source(
        &self,
        syntax: &TypeExpr,
    ) -> Option<ril_compiler_core::ids::TypeExprId> {
        self.callable_type_header(syntax)?.hir_id
    }

    fn callable_type_header<'a>(&'a self, mut syntax: &'a TypeExpr) -> Option<&'a TypeExpr> {
        let mut seen = BTreeSet::new();
        for _ in 0..64 {
            match &syntax.kind {
                TypeKind::Callable { .. } => return Some(syntax),
                TypeKind::Name { path, .. } => {
                    let name = path.join("::");
                    if !seen.insert(name.clone()) {
                        return None;
                    }
                    syntax = self.types.get(&name)?.value.as_ref()?;
                }
                _ => return None,
            }
        }
        None
    }

    /// A failed source reception must not suppress an independently required
    /// capability diagnostic. Probe the bound on a private value descriptor;
    /// keep its actual signature, return contracts and source witness intact.
    pub(super) fn check_receiving_callable_bounds_from(
        &mut self,
        value: &Value,
        syntax: &TypeExpr,
        source: &SignatureSource<'_>,
    ) -> BoundProbe {
        if let Some((_, annotations)) = self.callable_syntax(syntax, &mut BTreeSet::new()) {
            let mut constrained = value.clone();
            return self.ascribe_callable_bounds_from(
                &mut constrained,
                syntax,
                &annotations,
                source,
            );
        }
        // A source failure at a container must still expose its actual latent
        // child violations. Work in the existing definition transaction so
        // receiving ascription cannot replace any continuing field schema.
        let preview = self.snapshot_flow();
        let mut constrained = value.clone();
        self.ascribe_nested_callable_bounds_from(&mut constrained, syntax, source);
        self.restore_definition_state(&preview);
        BoundProbe::Unresolved
    }
    fn ascribe_projected_signature(
        &mut self,
        value: &mut Value,
        syntax: &TypeExpr,
        source: &SignatureSource<'_>,
        step: crate::sema::source_types::SourcePath,
    ) {
        match source.project(step) {
            Ok(source) => self.ascribe_signature_from(value, syntax, &source),
            Err(error) => self.unsupported(
                syntax.span,
                format!("signature Source path admission failed: {error}"),
            ),
        }
    }

    pub(super) fn ascribe_nested_callable_bounds_from(
        &mut self,
        value: &mut Value,
        syntax: &TypeExpr,
        source: &SignatureSource<'_>,
    ) {
        use crate::sema::source_types::SourcePath;
        let key = (
            syntax.span.file.0,
            syntax.span.start,
            syntax.span.end,
            value.cause.0,
        );
        if !self.nested_contracts.insert(key) {
            return;
        }
        let mut slots: Vec<(Slot, TypeExpr, SourcePath)> = Vec::new();
        match &syntax.kind {
            TypeKind::Record { fields, .. } => slots.extend(fields.iter().map(|field| {
                (
                    Slot::Field(field.name.clone()),
                    field.ty.clone(),
                    SourcePath::Field(field.name.clone()),
                )
            })),
            TypeKind::Tuple(items) => slots.extend(items.iter().enumerate().map(|(index, ty)| {
                (
                    Slot::Tuple(index as u32),
                    ty.clone(),
                    SourcePath::Tuple(index as u32),
                )
            })),
            TypeKind::Array { element, .. } => {
                for (node, slot) in self.fields.keys() {
                    if value.origins.nodes.contains(node)
                        && matches!(slot, Slot::Index(_) | Slot::AnyIndex)
                    {
                        slots.push((slot.clone(), *element.clone(), SourcePath::Element));
                    }
                }
            }
            TypeKind::Map {
                key,
                value: element,
            } => {
                for (node, slot) in self.fields.keys() {
                    if value.origins.nodes.contains(node) {
                        let (expected, projection) = if matches!(slot,Slot::Field(name)if name=="key")
                        {
                            (key, SourcePath::MapKey)
                        } else {
                            (element, SourcePath::MapValue)
                        };
                        slots.push((slot.clone(), *expected.clone(), projection));
                    }
                }
            }
            TypeKind::Optional(inner) => {
                if let Some(payload) = &mut value.option_payload {
                    self.ascribe_projected_signature(
                        payload,
                        inner,
                        source,
                        SourcePath::OptionalPayload,
                    );
                }
            }
            TypeKind::Name { path, arguments } => {
                let name = path.join("::");
                if let Some(declaration) = self.types.get(&name).cloned() {
                    if !declaration.nominal
                        && (!declaration.opaque || declaration.span.file == syntax.span.file)
                        && declaration.variants.is_empty()
                        && let Some(body) = declaration.value
                    {
                        if declaration.generics.is_empty() {
                            self.ascribe_signature_from(value, &body, source);
                        } else if syntax_contains_callable(&body) {
                            self.unsupported(syntax.span,"nested generic callable qualifications require instantiated syntax");
                        }
                    }
                } else {
                    let builtin = name.trim_start_matches("Prelude::");
                    match (builtin, arguments.as_slice()) {
                        ("Option", [inner]) => {
                            if let Some(payload) = &mut value.option_payload {
                                self.ascribe_projected_signature(
                                    payload,
                                    inner,
                                    source,
                                    SourcePath::OptionalPayload,
                                );
                            }
                        }
                        ("Result", [ok, error]) => {
                            if let Some(payload) = &mut value.result_success {
                                self.ascribe_projected_signature(
                                    payload,
                                    ok,
                                    source,
                                    SourcePath::ResultSuccess,
                                );
                            }
                            if let Some(payload) = &mut value.result_error {
                                self.ascribe_projected_signature(
                                    payload,
                                    error,
                                    source,
                                    SourcePath::ResultError,
                                );
                            }
                            if let Some(payload) = &mut value.result_payload
                                && let Some(success) = value.result_tag
                            {
                                self.ascribe_projected_signature(
                                    payload,
                                    if success { ok } else { error },
                                    source,
                                    if success {
                                        SourcePath::ResultSuccess
                                    } else {
                                        SourcePath::ResultError
                                    },
                                );
                            }
                        }
                        ("Immut", [inner]) => self.ascribe_signature_from(value, inner, source),
                        _ => {}
                    }
                }
            }
            _ => {}
        }
        for node in value.origins.nodes.clone() {
            for (slot, expected, projection) in &slots {
                if let Some(mut child) = self.fields.get(&(node, slot.clone())).cloned() {
                    self.ascribe_projected_signature(
                        &mut child,
                        expected,
                        source,
                        projection.clone(),
                    );
                    self.fields.insert((node, slot.clone()), child);
                }
            }
        }
        self.nested_contracts.remove(&key);
    }
    pub(super) fn check_callable_bounds(
        &mut self,
        value: &Value,
        callable: &Callable,
        owner: ScopeId,
        obligations: &InvocationSummary,
        span: Span,
    ) {
        let captures = self.contract_captures(callable);
        for bound in &value.callable_bounds {
            self.check_contract(bound, owner, obligations, span, &captures);
        }
    }
    fn contract_captures(&self, callable: &Callable) -> BTreeSet<BindingId> {
        match callable {
            Callable::Closure(id) => self.closures[*id].captures.clone(),
            Callable::Named(id, _) => self.functions[*id].captures.clone(),
            _ => BTreeSet::new(),
        }
    }
    pub(super) fn check_lambda_contract(
        &mut self,
        id: usize,
        frame: &Frame,
        result: &mut Value,
        span: Span,
    ) {
        let Some(contract) = self.lambda_contract(id).cloned() else {
            return;
        };
        if let Some(syntax) = &contract.return_type {
            let expected = self.ty(syntax);
            self.require_type(result, &expected, syntax.span);
            if frame.return_source_valid {
                let mut shape_frame = frame.clone();
                self.check_storage_shape(result, syntax, &mut shape_frame);
                if result.ty != Ty::Never {
                    result.ty = expected;
                }
            }
        }
        if !contract.annotations.is_empty() {
            let bound = CallableBound {
                annotations: contract.annotations,
                source: contract.source,
                typing_environment: contract.typing_environment,
                span: contract.span,
            };
            let captures = self.closures[id].captures.clone();
            self.check_contract(
                &bound,
                frame.owner,
                &InvocationSummary::from_obligations(&frame.obligations),
                span,
                &captures,
            );
        }
    }
    fn check_contract(
        &mut self,
        bound: &CallableBound,
        owner: ScopeId,
        obligations: &InvocationSummary,
        span: Span,
        captures: &BTreeSet<BindingId>,
    ) {
        self.with_typing_environment(&bound.typing_environment, |checker| {
            checker.check_contract_in_environment(bound, owner, obligations, span, captures);
        });
    }

    fn check_contract_in_environment(
        &mut self,
        bound: &CallableBound,
        owner: ScopeId,
        obligations: &InvocationSummary,
        span: Span,
        captures: &BTreeSet<BindingId>,
    ) {
        let mut effects = BTreeSet::new();
        let mut named = BTreeMap::new();
        let (
            mut state_axis,
            mut effect_axis,
            mut parameter_mut,
            mut retained,
            mut capture,
            mut closure,
        ) = (false, false, false, false, false, false);
        for annotation in &bound.annotations {
            let text = annotation.text.trim();
            if annotation.kind == AnnotationKind::Effect {
                effect_axis = true;
                effects.extend(self.effect_row(annotation));
                continue;
            }
            state_axis = true;
            match text {
                "&{}" => {}
                "&mut" => parameter_mut = true,
                "&^mut" => retained = true,
                "&capture" => capture = true,
                "&closure" => closure = true,
                _ if text.starts_with("&{") => {
                    let Some(group) = state_group(text) else {
                        self.error("E0538", annotation.span, "malformed state group", []);
                        continue;
                    };
                    let captured = group.capture_owner.is_some();
                    let header = group.capture_owner.unwrap_or("");
                    let mut layer = None;
                    for StateItem { mode, name } in group.items() {
                        let Some(&binding) = bound.typing_environment.contract_bindings().get(name)
                        else {
                            self.error(
                                "E0204",
                                annotation.span,
                                format!("unknown state source {name}"),
                                [],
                            );
                            continue;
                        };
                        let actual = self.bindings[binding].owner;
                        if captured {
                            if actual == ScopeId(0)
                                || actual == owner
                                || layer.is_some_and(|previous| previous != actual)
                            {
                                self.error(
                                    "E0538",
                                    annotation.span,
                                    "capture group must name one enclosing callable layer",
                                    [],
                                );
                            }
                            if !header.is_empty()
                                && self
                                    .scope_names
                                    .get(&actual)
                                    .and_then(|name| name.as_deref())
                                    != Some(header)
                            {
                                self.error(
                                    "E0538",
                                    annotation.span,
                                    "capture owner does not match the resolved source layer",
                                    [],
                                );
                            }
                            layer = Some(actual);
                        } else if actual != ScopeId(0) {
                            self.error(
                                "E0538",
                                annotation.span,
                                "global state group requires module storage",
                                [],
                            );
                        }
                        named
                            .entry(binding)
                            .and_modify(|old: &mut Mode| *old = (*old).max(mode))
                            .or_insert(mode);
                    }
                    if captured && layer.is_none() {
                        self.error(
                            "E0538",
                            annotation.span,
                            "capture group requires a source binding",
                            [],
                        );
                    }
                }
                _ => self.unsupported(
                    annotation.span,
                    "state provider bound requires a complete resolved provider contract",
                ),
            }
        }
        if effect_axis
            && obligations
                .effects
                .iter()
                .any(|effect| !effects.contains(effect))
        {
            self.error(
                "E0534",
                span,
                "actual invocation exceeds the callable effect bound",
                [],
            );
        }
        if state_axis {
            let outside = obligations.concrete_state.iter().any(|(&binding, mode)| {
                let binding = binding as usize;
                self.bindings[binding].owner != owner
                    && !named.get(&binding).is_some_and(|allowed| {
                        crate::sema::summary::Access::from(*allowed) >= *mode
                    })
                    && !(closure && captures.contains(&binding))
            });
            if outside
                || (obligations.parameter_write && !parameter_mut && !retained)
                || (obligations.retention && !retained)
                || (obligations.capture && !capture)
                || (obligations.handler_environment && !closure)
            {
                self.error(
                    "E0534",
                    span,
                    "actual invocation exceeds the callable capability bound",
                    [],
                );
            }
        }
    }
}

fn syntax_contains_callable(syntax: &TypeExpr) -> bool {
    match &syntax.kind {
        TypeKind::Callable { .. } => true,
        TypeKind::Tuple(items) => items.iter().any(syntax_contains_callable),
        TypeKind::Record { fields, .. } => fields
            .iter()
            .any(|field| syntax_contains_callable(&field.ty)),
        TypeKind::Array { element, .. } | TypeKind::Optional(element) => {
            syntax_contains_callable(element)
        }
        TypeKind::Map { key, value } => {
            syntax_contains_callable(key) || syntax_contains_callable(value)
        }
        _ => false,
    }
}

#[cfg(test)]
mod frozen_effect_scope_tests {
    use super::*;

    #[test]
    fn callable_effect_bounds_use_the_captured_type_instance_and_restore_the_caller() {
        let parsed = ril_syntax::parse(
            "eff Read<S>{get()->S}\nfn seed<T>(value:T){}\nfn caller<T>(value:T){}",
        );
        assert!(parsed.diagnostics.is_empty());
        let mut checker = Checker::new(FileId(0));
        checker.run(&parsed.program);
        let seed = checker
            .functions
            .iter()
            .position(|info| info.syntax.name == "seed")
            .unwrap();
        checker.generic_scope(seed);
        let identity = checker.type_source.environment.generic_context["T"].clone();
        let mut captured = checker.capture_typing_environment().thaw();
        captured
            .generic_substitutions
            .insert(identity.clone(), Ty::Int("int".into()));
        let captured = captured.freeze();
        let caller_function = checker
            .functions
            .iter()
            .position(|info| info.syntax.name == "caller")
            .unwrap();
        checker.generic_scope(caller_function);
        let caller_identity = checker.type_source.environment.generic_context["T"].clone();
        assert_ne!(identity, caller_identity);
        let mut caller = checker.capture_typing_environment().thaw();
        caller
            .generic_substitutions
            .insert(caller_identity.clone(), Ty::Str);
        let caller = caller.freeze();
        let span = checker.functions[seed].syntax.span;
        let annotation = Annotation {
            kind: AnnotationKind::Effect,
            text: "@Read<T>".into(),
            span,
        };
        checker.restore_typing_environment(captured.clone());
        let captured_effects = checker.effect_row(&annotation);
        checker.restore_typing_environment(caller.clone());
        let caller_effects = checker.effect_row(&annotation);
        assert!(!captured_effects.is_empty());
        assert_ne!(captured_effects, caller_effects);
        checker.diagnostics.clear();
        let bound = CallableBound {
            source: None,
            annotations: vec![annotation],
            typing_environment: captured,
            span,
        };
        let mut obligations = InvocationSummary {
            effects: captured_effects,
            ..Default::default()
        };
        checker.check_contract(&bound, ScopeId(0), &obligations, span, &BTreeSet::new());
        assert!(
            checker.diagnostics.is_empty(),
            "captured instance was replaced by caller: {:?}",
            checker.diagnostics
        );
        assert_eq!(
            checker.type_source.environment.generic_substitutions[&caller_identity],
            Ty::Str
        );
        obligations.effects = caller_effects;
        checker.check_contract(&bound, ScopeId(0), &obligations, span, &BTreeSet::new());
        assert!(
            checker
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0534")
        );
        assert_eq!(
            checker.type_source.environment.generic_substitutions[&caller_identity],
            Ty::Str
        );
    }
}
