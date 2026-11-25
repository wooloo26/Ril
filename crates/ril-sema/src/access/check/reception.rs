use super::*;
use crate::ty::reception;

impl Analyzer<'_> {
    pub(super) fn shadow_type(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        ty: ril_frontend::syntax::TypeId,
    ) {
        use ril_frontend::syntax::{GenericArg, Type};
        match &self.ast(ctx.file).ty(ty).value {
            Type::TypeOf(expr) => {
                let mut shadow = ctx.clone();
                shadow.shadow = true;
                shadow.loop_owner = None;
                let mut slots = ledger.clone();
                slots.clear_result_obligations();
                let result = self.expr(&mut shadow, &mut slots, *expr);
                self.check_results(&slots, &result.root_results());
            }
            Type::Named(path) => {
                for parameter in path.segments.iter().flat_map(|segment| &segment.arguments) {
                    if let GenericArg::Type(ty) = parameter {
                        self.shadow_type(ctx, ledger, *ty);
                    }
                }
            }
            Type::Array(_, ty) | Type::Option(ty) | Type::Project { base: ty, .. } => {
                self.shadow_type(ctx, ledger, *ty);
            }
            Type::Result(left, right) | Type::Map(left, _, right) => {
                self.shadow_type(ctx, ledger, *left);
                self.shadow_type(ctx, ledger, *right);
            }
            Type::Tuple(items) => {
                for (_, ty) in items {
                    self.shadow_type(ctx, ledger, *ty);
                }
            }
            Type::Record { fields, .. } => {
                for field in fields {
                    self.shadow_type(ctx, ledger, field.ty);
                }
            }
            Type::Callable(call) => {
                for ty in call.params.iter().filter_map(|param| param.ty) {
                    self.shadow_type(ctx, ledger, ty);
                }
                self.shadow_type(ctx, ledger, call.result);
            }
            _ => {}
        }
    }

    pub(super) fn retarget(value: &mut Datum, path: &[reception::Step], mode: Access) -> bool {
        let Some((step, rest)) = path.split_first() else {
            if value.roots.iter().any(|root| !root.new) {
                return false;
            }
            for root in &mut value.roots {
                root.fix_mode(mode);
                root.clone_member = false;
            }
            return true;
        };
        let coordinate = match step {
            reception::Step::Field(name) => Coordinate::Field(name.clone()),
            reception::Step::Position(index) => Coordinate::Index(index.to_string()),
            reception::Step::Elements => {
                return if value.members.is_empty() {
                    value.roots.iter().all(|root| root.new)
                } else {
                    value
                        .members
                        .values_mut()
                        .all(|member| Self::retarget(member, rest, mode))
                };
            }
        };
        if let Some(member) = value.members.get_mut(&coordinate) {
            Self::retarget(member, rest, mode)
        } else {
            value.origins().all(|origin| origin.new)
        }
    }

    pub(super) fn receive_member(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        mut value: Datum,
        mode: Access,
        span: Span,
    ) -> Datum {
        if mode != Access::Immutable {
            value.forget_collection_layout();
        }
        if value.roots.is_empty() {
            return value;
        }
        if mode == Access::Shared {
            self.check_shared_reception(&value, span);
        }
        if mode == Access::Immutable
            && self.require_snapshot(
                (ctx, ledger),
                &ledger.snapshot(&value),
                Code::E0535,
                span,
                "live authority cannot enter an immutable member",
            )
        {
            value.specialize_snapshot_sources();
        }
        let inline_closure = value.environments.contains(&span);
        if value.requires_new || inline_closure {
            if mode == Access::Mut
                && inline_closure
                && value
                    .members
                    .values()
                    .flat_map(Datum::origins)
                    .any(|capture| capture.mode.writes())
            {
                self.error(
                    Code::E0510,
                    span,
                    "a closure retaining a writer needs shared writable storage",
                );
            }
            for root in &mut value.roots {
                root.fix_mode(mode);
            }
            return value;
        }
        let valid = value.roots.iter().all(|root| root.mode == mode);
        if !valid {
            let code = match mode {
                Access::Immutable => Code::E0535,
                Access::Ref => Code::E0357,
                Access::Mut if value.writers() => Code::E0510,
                Access::Mut | Access::Shared => Code::E0522,
            };
            self.error(
                code,
                span,
                "existing source does not match the member's access mode",
            );
        }
        if mode == Access::Mut && value.writers() {
            self.error(
                Code::E0510,
                span,
                "mutable member requires an exclusive handoff",
            );
        }
        for root in &mut value.roots {
            root.explicit_share = false;
        }
        value
    }

    pub(super) fn require_snapshot(
        &mut self,
        (ctx, ledger): (&Context, &Ledger),
        value: &Datum,
        code: Code,
        span: Span,
        message: &'static str,
    ) -> bool {
        let mut conditions = BTreeMap::<_, BTreeSet<_>>::new();
        if !value.accepts_snapshot_sources(&mut |origin| {
            let Some(expression) = origin.forwarded_mode() else {
                return false;
            };
            let owner = origin.entry_callable().unwrap_or(ctx.owner);
            conditions.entry(owner).or_default().insert(expression);
            true
        }) {
            self.error(code, span, message);
            return false;
        }
        // A symbolic path can be treated as immutable after this reception.
        // Keep only the mode assignments for which all such paths are plain.
        if ctx.reachable && !ctx.shadow {
            self.snapshots.freeze(ledger, value);
            self.mode_constraints
                .extend(conditions.into_iter().map(|(owner, expressions)| {
                    domains::ModeConstraint {
                        owner,
                        conditions: Vec::new(),
                        test: domains::ModeTest::Immutable(expressions, code),
                        span,
                        message,
                    }
                }));
        }
        true
    }

    pub(super) fn freeze_value(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        value: &mut Datum,
        span: Span,
    ) {
        *value = ledger.snapshot(value);
        self.require_snapshot(
            (ctx, ledger),
            value,
            Code::E0535,
            span,
            "live authority cannot be frozen as a plain snapshot",
        );
        value.freeze();
    }

    pub(super) fn require_shared_replacement(
        &mut self,
        value: &Datum,
        span: Span,
        allow_new: bool,
    ) {
        if value
            .roots
            .iter()
            .any(|root| !(root.explicit_share || allow_new && root.new))
        {
            self.error(
                Code::E0510,
                span,
                "shared replacement requires a '^mut' expression",
            );
        }
    }

    pub(super) fn check_exclusive_reception(&mut self, value: &Datum, span: Span) {
        // A Draft projection remains confined to the derive callback.
        if value.requires_new || value.writers() && value.roots.iter().all(|root| root.draft) {
            return;
        }
        if value.writers() {
            self.error(
                Code::E0510,
                span,
                "a persistent mutable binding requires an exclusive handoff",
            );
        } else {
            self.error(
                Code::E0520,
                span,
                "binding cannot manufacture write authority",
            );
        }
    }

    pub(super) fn check_shared_reception(&mut self, value: &Datum, span: Span) {
        if value
            .roots
            .iter()
            .any(|root| root.call_scoped_access && root.mode.writes())
        {
            self.error(Code::E0528, span, "a call-scoped writer cannot be shared");
        }
    }

    pub(super) fn shared_local_input(
        &mut self,
        ctx: &Context,
        declaration: Span,
        value: &Datum,
        span: Span,
    ) {
        let closure_with_writer =
            value.creates_environment() && value.origins().any(|origin| origin.mode.writes());
        if !value.writers() && !closure_with_writer {
            self.error(
                Code::E0527,
                span,
                "shared binding requires a writable source",
            );
            return;
        }
        self.check_shared_reception(value, span);
        let existing_writer = value.roots.iter().any(|root| {
            root.mode.writes() && !(root.new && (value.requires_new || root.explicit_share))
        });
        if existing_writer || closure_with_writer {
            self.seed(ctx, Obligation::SharedReception(declaration));
        }
    }

    pub(super) fn require_shared_local(&mut self, ctx: &Context, declaration: Span, value: &Datum) {
        self.requirement(
            ctx,
            declaration,
            Obligation::SharedReception(declaration),
            "shared binding requires reachable reception of a shared writer",
        );
        self.shared_local_input(ctx, declaration, value, declaration);
    }

    pub(super) fn check_ref_binding(&mut self, span: Span, value: &Datum, variable: bool) {
        if value.roots.iter().any(|root| root.explicit_share) {
            self.error(
                Code::E0527,
                span,
                "a ref binding does not use a '^mut' marker",
            );
        } else if value.roots.iter().any(|root| root.from_variable) {
            self.error(
                Code::E0531,
                span,
                "a reassignable binding cannot anchor a ref view",
            );
        } else if value.roots.is_empty() {
            self.error(Code::E0531, span, "ref binding has no live object source");
        } else if (value.requires_new
            || value
                .roots
                .iter()
                .any(|root| root.new && root.dependencies.is_empty()))
            && (variable
                || !value
                    .members
                    .values()
                    .flat_map(Datum::origins)
                    .any(|source| source.mode == Access::Ref && !source.new))
        {
            self.error(
                Code::E0543,
                span,
                "temporary has no live ref source to anchor the binding",
            );
        }
    }

    pub(super) fn check_ref_scope(&mut self, span: Span, value: &Datum, destination: Span) {
        let shorter_scope = value
            .roots
            .iter()
            .flat_map(|root| &root.anchor_scopes)
            .any(|source| {
                source.file != destination.file
                    || source.start > destination.start
                    || source.end < destination.end
            });
        if shorter_scope {
            self.error(
                Code::E0604,
                span,
                "ref source scope must enclose the reassignable binding's scope",
            );
        }
    }

    pub(super) fn returned(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        value: Datum,
        span: Span,
    ) {
        let mut value = ledger.snapshot_call_graph(&value);
        ledger.inspect(&value);
        if value.origins().any(|origin| origin.confined.is_some()) {
            self.error(Code::E0604, span, "confined authority cannot be returned");
        }
        if !ctx.runtime || ctx.shadow {
            return;
        }
        self.storage_exit(ctx, ledger);
        if value.creates_environment() {
            self.seed(ctx, Obligation::Capture);
        }
        if value.returns_call_scoped_writer(ctx.expected) {
            self.error(
                Code::E0528,
                span,
                "a call-scoped writer cannot escape in a return",
            );
        }
        match ctx.expected {
            Mode::Plain if value.requires_new => self.error(
                Code::E0544,
                ctx.owner,
                "fresh shared return must declare -> new",
            ),
            Mode::Plain => {
                if self.require_snapshot(
                    (ctx, ledger),
                    &value,
                    Code::E0528,
                    span,
                    "plain return cannot expose live authority",
                ) {
                    value.specialize_snapshot_sources();
                }
            }
            Mode::New if !value.requires_new => {
                self.error(Code::E0546, span, "return does not have new qualification");
            }
            Mode::Ref | Mode::Shared
                if value.roots.is_empty()
                    || value
                        .roots
                        .iter()
                        .any(|root| !ctx.returns.contains(&root.region.source)) =>
            {
                self.error(
                    Code::E0545,
                    span,
                    "return does not select its declared entry source",
                );
            }
            Mode::Shared if value.roots.iter().any(|root| root.mode != Access::Shared) => {
                self.error(
                    Code::E0528,
                    span,
                    "shared return requires an existing shared writer",
                );
            }
            _ => {}
        }
        if ctx.expected == Mode::Shared {
            for origin in &value.roots {
                self.seed(ctx, Obligation::Retain(origin.region.source));
            }
        }
        let actual: BTreeSet<_> = value
            .members
            .values()
            .filter(|_| ctx.expected != Mode::Plain)
            .flat_map(Datum::origins)
            .filter(|origin| !origin.new && ctx.formals.contains(&Some(origin.region.source)))
            .map(|origin| (origin.mode, origin.region.source))
            .collect();
        if ctx.expected != Mode::Infer
            && actual
                .iter()
                .any(|source| !ctx.declared_contained.contains(source))
        {
            self.error(Code::E0510, ctx.owner, "missing contained return source");
        }
        for &(_, source) in actual.iter().filter(|(mode, _)| *mode == Access::Shared) {
            self.seed(ctx, Obligation::Retain(source));
            self.seed(ctx, Obligation::Share(source));
        }
        ctx.return_values.push(value);
    }

    pub(super) fn storage_exit(&mut self, ctx: &Context, ledger: &Ledger) {
        if !ctx.in_function
            || !ctx.runtime
            || ctx.shadow
            || !ctx.reachable
            || ledger.no_continuation
        {
            return;
        }
        self.publish_at_exit(ctx, ledger, true);
        self.storage_exits
            .entry(ctx.owner)
            .or_default()
            .push(storage::StorageExit {
                updates: ledger.call_updates(ctx.owner, &ctx.formals, &ctx.caller_slots),
                flow: ledger.storage_flow.clone(),
            });
    }

    pub(super) fn publish_at_exit(&mut self, ctx: &Context, ledger: &Ledger, normal: bool) {
        if !ctx.runtime || ctx.shadow || !ctx.reachable {
            return;
        }
        for &slot in ctx.caller_slots.iter().chain(ctx.formals.iter().flatten()) {
            let Some(slot) = ledger.slots.get(&slot) else {
                continue;
            };
            let caller_root = !ctx.new_formals.contains(&slot.decl);
            let value = ledger.snapshot(&slot.value);
            value.surviving_publications(ctx.owner, caller_root, &mut |stored| {
                if stored.creates_environment() {
                    self.seed(ctx, Obligation::Capture);
                }
                for origin in stored
                    .origins()
                    .filter(|origin| origin.mode == Access::Shared)
                {
                    self.seed(ctx, Obligation::Retain(origin.region.source));
                    let modeled = ctx.formals.contains(&Some(slot.decl))
                        || ledger.replaces_slot(ctx.owner, slot.decl);
                    let effect = if normal && modeled {
                        Obligation::StoreShare(origin.region.source)
                    } else {
                        Obligation::Share(origin.region.source)
                    };
                    self.seed(ctx, effect);
                }
            });
        }
    }

    pub(super) fn check_publication_source(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        value: &Datum,
        span: Span,
    ) {
        let value = ledger.loop_snapshot(value);
        self.check_stored_views(&value, false, span);
        if value
            .origins()
            .any(|origin| origin.call_scoped_access && origin.mode.writes())
        {
            self.error(
                Code::E0528,
                span,
                "a call-scoped writer cannot be retained in caller storage",
            );
        }
        for origin in value.origins().filter(|origin| {
            origin.mode == Access::Shared
                && origin.region.selection.is_empty()
                && ctx.via.contains(&origin.region.source)
        }) {
            self.seed(ctx, Obligation::NeedsSharing(origin.region.source));
        }
    }

    pub(super) fn check_stored_views(&mut self, value: &Datum, root_as_ref: bool, span: Span) {
        if value
            .origins()
            .any(|origin| origin.mode == Access::Ref && origin.call_scoped_access)
            || root_as_ref && value.roots.iter().any(|origin| origin.call_scoped_access)
        {
            self.error(
                Code::E0604,
                span,
                "a ref view of a call-scoped writer cannot be stored in existing storage",
            );
        }
    }

    pub(super) fn check_results(&mut self, ledger: &Ledger, except: &BTreeSet<ResultOccurrence>) {
        let pending: BTreeSet<_> = ledger
            .pending_results()
            .filter(|item| !except.contains(item))
            .map(|item| item.span)
            .chain(ledger.lost_results.iter().copied())
            .collect();
        for span in pending {
            self.error(
                Code::E0720,
                span,
                "fallible result has not been inspected on normal exit",
            );
        }
    }

    pub(super) fn discard(&mut self, ledger: &Ledger, value: &Datum) {
        for item in value
            .results()
            .iter()
            .filter(|item| !ledger.result_inspected(item))
        {
            self.error(Code::E0720, item.span, "discarded fallible result");
        }
    }

    pub(super) fn references_scoped_resource(&self, value: &Datum) -> bool {
        value.origins().any(|origin| {
            origin
                .confined
                .is_some_and(|scope| self.cleanups.contains_key(&scope))
        })
    }

    pub(super) fn check_resource_binding(&mut self, name: Span, value: &Datum, resource: bool) {
        let value_type = self
            .definition(name)
            .and_then(|id| self.program.bindings.get(&id))
            .is_some_and(Ty::is_value);
        if !resource && !value_type && self.references_scoped_resource(value) {
            self.error(Code::E0604, name, "scoped resource cannot be rebound");
        }
    }

    pub(super) fn cleanup(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        value: &mut Datum,
        value_span: Span,
        binding: Span,
        mode: Mode,
    ) {
        if self.references_scoped_resource(value) {
            self.error(
                Code::E0604,
                binding,
                "scoped resource already has a cleanup binding",
            );
            return;
        }
        if matches!(self.ty(value_span), Ty::Sender(_)) {
            if !value.requires_new {
                self.error(
                    Code::E0548,
                    binding,
                    "cleanup requires a new-qualified sender",
                );
            }
            value.transform(&mut |origin| {
                origin.confined = Some(binding);
                origin.fix_mode(if mode == Mode::Mut {
                    Access::Mut
                } else {
                    Access::Ref
                });
            });
            self.cleanups.insert(binding, CleanupAction::CloseSender);
            return;
        }
        let Ty::Adt(adt) = self.ty(value_span) else {
            self.error(
                Code::E0541,
                binding,
                "resource type has no cleanup declaration",
            );
            return;
        };
        let def = self.program.hir.definition(adt.definition);
        let ast = self.ast(def.name.span.file);
        let cleanup = def
            .stmt
            .and_then(|id| match &ast.stmt(id).value.kind {
                StmtKind::Type(decl) => decl.cleanup.as_ref(),
                _ => None,
            })
            .and_then(|name| self.definition(name.span));
        let Some(cleanup) = cleanup else {
            self.error(
                Code::E0541,
                binding,
                "resource type has no cleanup function",
            );
            return;
        };
        let Some(signature) = self.program.callables.get(&cleanup) else {
            self.error(
                Code::E0541,
                binding,
                "cleanup is not a callable declaration",
            );
            return;
        };
        let [parameter] = signature.parameters.as_slice() else {
            self.error(
                Code::E0541,
                binding,
                "cleanup must take one resource argument",
            );
            return;
        };
        if signature.result != Ty::Unit
            || !matches!(parameter.mode, Mode::Ref | Mode::Mut | Mode::New)
            || signature
                .state
                .iter()
                .any(|clause| matches!(clause.as_str(), "^mut" | "capture" | "up"))
            || (parameter.mode == Mode::Mut) != signature.state.iter().any(|clause| clause == "mut")
            || !matches!(&parameter.ty, Ty::Adt(owner) if owner.definition == adt.definition)
        {
            self.error(
                Code::E0541,
                binding,
                "cleanup must take new, mut, or ref Self and return ()",
            );
        }
        if signature.effects.iter().any(|effect| effect == "fiber") {
            self.error(Code::E0616, binding, "@fiber is prohibited on cleanup");
        }
        if let Some(export) = self.program.imported_functions.get(&cleanup) {
            let owner = self.program.hir.definition(cleanup).name.span;
            self.charge_imported_effects(ctx, ledger, owner, signature, &export.summary, binding);
        } else {
            for effect in &signature.effects {
                self.effect(ctx, ledger, effect, binding);
            }
        }
        if parameter.mode == Mode::New && !value.requires_new {
            self.error(
                Code::E0548,
                binding,
                "cleanup requires a new-qualified resource",
            );
        }
        if parameter.mode == Mode::Mut || mode == Mode::Mut {
            if !value.writers() {
                self.error(
                    Code::E0520,
                    binding,
                    "cleanup requires writable resource authority",
                );
            } else if parameter.mode == Mode::Mut {
                self.mutate(ctx, ledger, value, binding);
            }
        }
        value.transform(&mut |origin| {
            origin.confined = Some(binding);
            origin.fix_mode(if mode == Mode::Mut {
                Access::Mut
            } else {
                Access::Ref
            });
        });
        self.cleanups
            .insert(binding, CleanupAction::Function(cleanup));
    }
}
