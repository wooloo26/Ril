use super::*;

impl<'a> Analyzer<'a> {
    pub(super) fn check_live(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        value: &Datum,
        span: Span,
        message: &'static str,
    ) {
        if !ctx.reachable {
            return;
        }
        if ledger.is_revoked(value) {
            self.error(Code::E0549, span, message);
        }
    }

    pub(super) fn consume_linear(&mut self, ctx: &Context, ledger: &mut Ledger, value: &mut Datum) {
        if !ctx.reachable {
            return;
        }
        if let Some(root) = value
            .roots
            .iter()
            .find(|root| root.mode == Access::Ref || root.call_scoped_access)
        {
            self.error(
                Code::E0528,
                root.region.source,
                "cannot consume a linear value through call-scoped ref or mut access",
            );
            return;
        }
        ledger.consume_datum_linear(value);
        for root in &value.roots {
            for &dependency in &root.dependencies {
                ledger.revoke(dependency, Some(root));
            }
        }
        value.clear_linear();
        value.transform(&mut |origin| {
            origin.dependencies.clear();
            origin.new = true;
        });
    }

    pub(super) fn place(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        id: ExprId,
        prior: Datum,
    ) -> Datum {
        let ast = self.ast(ctx.file);
        match &ast.expr(id).value {
            Expr::Member { base, member, .. } => {
                let value = self.expr(ctx, ledger, *base);
                let coordinate = self.coordinate(ctx, ledger, member);
                let (_, variable) = self.member_schema(ast.expr(*base).span, &coordinate);
                if variable || value.origins().any(|origin| origin.draft) {
                    if value.origins().any(|origin| origin.draft)
                        && let Ty::Adt(adt) = self.ty(ast.expr(*base).span)
                        && self.program.has_type_invariants(adt.definition)
                    {
                        self.error(
                            Code::E0536,
                            ast.expr(id).span,
                            "cannot mutate through a draft of a type with a static invariant; replace the whole value instead",
                        );
                        return Datum::default();
                    }
                    value.slot_projection(coordinate)
                } else {
                    Datum::default()
                }
            }
            Expr::Index { base, index, .. } => {
                let value = self.expr(ctx, ledger, *base);
                let coordinate =
                    self.collection_coordinate(ctx, self.ty(ast.expr(*base).span), *index);
                value.slot_projection(coordinate)
            }
            _ => prior,
        }
    }

    pub(super) fn write(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        target: ExprId,
        prior: &Datum,
        value: Datum,
        span: Span,
    ) {
        let node = self.ast(ctx.file).expr(target);
        if let Expr::Path(path) = &node.value {
            if let Some(id) = self.declaration(path.span)
                && let Some((decl, mode, variable)) = ledger
                    .slots
                    .get(&id)
                    .map(|slot| (slot.decl, slot.mode, slot.variable))
            {
                if !variable {
                    let code = if mode == Mode::Plain {
                        Code::E0501
                    } else {
                        Code::E0502
                    };
                    let mut diag =
                        Diagnostic::error(code, node.span, "binding cannot be reassigned");
                    if decl != node.span {
                        diag = diag.with_label(decl, "binding declared here without `var`");
                    }
                    diag = diag
                        .with_help("declare the binding with `var` if the slot must be replaced");
                    self.error_diag(diag);
                    return;
                }
                self.seed(ctx, Obligation::Replace(decl));
                for origin in value.origins().filter(|origin| origin.draft) {
                    if origin
                        .confined
                        .is_some_and(|scope| decl.start < scope.start)
                    {
                        self.error(
                            Code::E0607,
                            span,
                            "draft cannot be assigned to an outer slot",
                        );
                    }
                }
                let mut value = value;
                if mode == Mode::Shared {
                    self.require_shared_replacement(&value, span, false);
                    self.shared_local_input(ctx, decl, &value, span);
                } else if mode == Mode::Mut {
                    self.check_exclusive_reception(&value, span);
                } else if mode == Mode::Ref {
                    if value.roots.iter().any(|root| root.mode != Access::Ref) {
                        self.error(
                            Code::E0357,
                            span,
                            "ref slot replacement requires a ref expression",
                        );
                    } else {
                        self.check_ref_binding(span, &value, true);
                        if let Some(scope) = self.binding_scopes.get(&decl).copied() {
                            self.check_ref_scope(span, &value, scope);
                        }
                    }
                }
                let captured = ctx.caller_slots.contains(&id);
                if captured {
                    self.check_publication_source(ctx, ledger, &value, span);
                }
                if mode == Mode::Plain {
                    self.freeze_value(ctx, ledger, &mut value, span);
                } else {
                    value.receive_binding(Access::from_mode(mode));
                }
                value.transform(&mut |origin| {
                    origin.dependencies.insert(decl.into());
                });
                if captured {
                    value.publications.insert(ctx.owner, true);
                }
                ledger.replace_slot(id, value, true);
                return;
            }
            self.error(
                Code::E0501,
                node.span,
                "assignment requires a replaceable local slot",
            );
            return;
        }
        let (Expr::Member { base, .. } | Expr::Index { base, .. }) = node.value else {
            self.error(Code::E0503, node.span, "invalid assignment target");
            return;
        };
        if matches!(node.value, Expr::Index { .. } | Expr::Member { .. })
            && self.program.is_must_consume(self.ty(node.span))
        {
            self.error(
                Code::E0625,
                span,
                "cannot overwrite a must-consume slot; use Map::replace or destructure first",
            );
            return;
        }
        self.mutate(ctx, ledger, prior, span);
        self.check_draft_insertion(ctx, ledger, prior, &value, span);
        if let Some(coordinate) = prior
            .roots
            .first()
            .and_then(|origin| origin.region.selection.last())
        {
            let access = self
                .member_schema(self.ast(ctx.file).expr(base).span, coordinate)
                .0;
            if ctx.reachable
                && !value.roots.is_empty()
                && results::carries_result(self.program, self.hir_scope(ctx), self.ty(node.span))
            {
                ledger.lose_collection_elements_at(prior);
            }
            self.store_member((ctx, ledger), prior, value, access, span);
        }
    }

    pub(super) fn store_member(
        &mut self,
        (ctx, ledger): (&Context, &mut Ledger),
        place: &Datum,
        value: Datum,
        access: Access,
        span: Span,
    ) {
        if ledger
            .loop_snapshot(&value)
            .origins()
            .any(|origin| origin.confined.is_some())
        {
            self.error(
                Code::E0604,
                span,
                "confined value cannot be stored in an outer object",
            );
        }
        if place.origins().any(|origin| {
            let source = origin.region.source;
            ctx.caller_sources.contains(&source)
                || ctx.formals.contains(&Some(source))
                    && (!ctx.new_formals.contains(&source) || !origin.new)
        }) {
            self.check_publication_source(ctx, ledger, &value, span);
        }
        if !ctx.reachable || value.roots.is_empty() {
            return;
        }
        if access == Access::Ref {
            self.check_stored_views(&ledger.loop_snapshot(&value), true, span);
        }
        if access == Access::Shared {
            self.require_shared_replacement(&value, span, true);
        }
        let mut value = self.receive_member(ctx, ledger, value, access, span);
        value
            .publications
            .insert(ctx.owner, place.roots.iter().any(|root| !root.new));
        ledger.replace_member(place, value, true);
    }

    pub(super) fn check_draft_insertion(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        target: &Datum,
        value: &Datum,
        span: Span,
    ) {
        if target.roots.iter().any(|root| root.draft) {
            let snapshot = ledger.loop_snapshot(value);
            let message =
                "draft insertion requires an immutable snapshot or an isolated local value";
            if snapshot.origins().any(|origin| {
                origin.new
                    && origin.mode != Access::Immutable
                    && ctx.caller_sources.contains(&origin.region.source)
            }) {
                self.error(Code::E0535, span, message);
            } else {
                self.require_snapshot((ctx, ledger), &snapshot, Code::E0535, span, message);
            }
        }
    }

    pub(super) fn mutate(&mut self, ctx: &Context, ledger: &Ledger, value: &Datum, span: Span) {
        if !value.writers() {
            self.error(Code::E0520, span, "write requires writable authority");
        }
        if ledger.slots.values().any(|slot| {
            slot.mode == Mode::Ref
                && slot.value.origins().any(|held| {
                    held.region.selection.iter().any(|coordinate| {
                        matches!(coordinate, Coordinate::Index(_) | Coordinate::Dynamic)
                    }) && value.origins().any(|written| held.overlaps(written))
                })
        }) {
            self.error(
                Code::E0537,
                span,
                "collection mutation overlaps a scoped element view",
            );
        }
        if ledger.iteration.iter().any(|iterable| {
            value.origins().any(|written| {
                iterable.origins().any(|iterator| {
                    written.overlaps(iterator)
                        && written.region.selection.len() <= iterator.region.selection.len()
                })
            })
        }) {
            self.error(Code::E0526, span, "collection is already being iterated");
        }
        for conflict in ledger.hold_conflicts(value, Mode::Mut) {
            self.check_conflict(
                ctx,
                conflict,
                None,
                span,
                "write overlaps an active lexical handler hold",
            );
        }
        self.require_schema(ctx, value, SchemaRequirement::Writable);
        self.record_write(ctx, value);
    }

    pub(super) fn record_write(&mut self, ctx: &Context, value: &Datum) {
        for origin in &value.roots {
            if !origin.new {
                self.seed(ctx, Obligation::WriteExisting(origin.region.source));
            }
            for id in origin
                .dependency_spans()
                .chain(std::iter::once(origin.region.source))
            {
                self.seed(ctx, Obligation::Write(id));
            }
        }
    }

    pub(super) fn schema_requirements(
        &self,
        value: &Datum,
        mode: SchemaRequirement,
    ) -> BTreeSet<Obligation> {
        value
            .roots
            .iter()
            .flat_map(|origin| {
                origin
                    .reception
                    .iter()
                    .enumerate()
                    .filter_map(move |(index, step)| {
                        let Reception::Axis(path) = step else {
                            return None;
                        };
                        let axis = self.schema_axis(path)?.clone();
                        let mode = if index + 1 == origin.reception.len() {
                            mode
                        } else {
                            SchemaRequirement::Writable
                        };
                        Some(Obligation::Schema(axis, mode))
                    })
            })
            .collect()
    }

    pub(super) fn require_schema(&mut self, ctx: &Context, value: &Datum, mode: SchemaRequirement) {
        for obligation in self.schema_requirements(value, mode) {
            self.seed(ctx, obligation);
        }
    }

    pub(super) fn coordinate(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        member: &Member,
    ) -> Coordinate {
        match member {
            Member::Name(name) => Coordinate::Field(name.value.clone()),
            Member::Index(index) => Coordinate::Index(index.value.clone()),
            Member::Computed(id) => {
                self.expr(ctx, ledger, *id);
                if let Some(Value::Str(key)) = self
                    .program
                    .static_values
                    .get(&self.ast(ctx.file).expr(*id).span)
                {
                    Coordinate::Field(key.clone())
                } else {
                    self.index_coordinate(ctx, *id)
                }
            }
        }
    }

    pub(super) fn index_coordinate(&self, ctx: &Context, id: ExprId) -> Coordinate {
        match &self.ast(ctx.file).expr(id).value {
            Expr::Literal(value) if value.kind == LiteralKind::Int => {
                if let Ok(Value::Int(index)) = ty::literal(value) {
                    Coordinate::Index(index.to_string())
                } else {
                    Coordinate::Dynamic
                }
            }
            _ => Coordinate::Dynamic,
        }
    }

    pub(super) fn collection_coordinate(&self, ctx: &Context, ty: &Ty, id: ExprId) -> Coordinate {
        let ty = if let Ty::Draft(inner) = ty { inner } else { ty };
        if matches!(ty, Ty::Map(..)) {
            self.constant_map_key(ctx, id)
                .unwrap_or(Coordinate::Dynamic)
        } else {
            self.index_coordinate(ctx, id)
        }
    }

    pub(super) fn project_index(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        value: &Datum,
        (ty, index, span): (&Ty, ExprId, Span),
    ) -> Datum {
        if let Expr::Range {
            start,
            end,
            inclusive,
        } = self.ast(ctx.file).expr(index).value
        {
            let Some(element) = self.schema_member(ty, &Coordinate::Dynamic) else {
                return Datum::default();
            };
            let bound = |id| match self.index_coordinate(ctx, id) {
                Coordinate::Index(index) => index.parse::<usize>().ok(),
                _ => None,
            };
            let start = start.map_or(Some(0), bound);
            let end = end.map_or_else(
                || self.slice_source_length(ledger, value),
                |end| bound(end).and_then(|bound| bound.checked_add(usize::from(inclusive))),
            );
            return self.array_slice(ctx, ledger, value, &element, (start, end), span);
        }
        let coordinate = self.collection_coordinate(ctx, ty, index);
        let mode = self.schema_mode(ty, &coordinate).0;
        self.project_observed(ctx, ledger, value, (coordinate, mode, span))
    }

    pub(super) fn project_observed(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        base: &Datum,
        (coordinate, mode, span): (Coordinate, Mode, Span),
    ) -> Datum {
        let mut selected = ledger.project_schema(base, coordinate.clone(), mode);
        if ctx.reachable
            && ctx.runtime
            && !ctx.shadow
            && ledger.storage_flow.is_some()
            && !self.program.is_value(self.ty(span))
            && !selected.roots.is_empty()
        {
            let index =
                self.storage_read_index(storage::ReadSite::Source(span, coordinate.clone()));
            ledger.record_storage_read(index, base, coordinate, mode, &mut selected);
        }
        selected
    }

    pub(super) fn storage_read_index(&mut self, site: storage::ReadSite) -> usize {
        let next = self.storage_read_sites.len();
        *self.storage_read_sites.entry(site).or_insert(next)
    }

    pub(super) fn slice_source_length(&self, ledger: &Ledger, array: &Datum) -> Option<usize> {
        // A deferred callback can change the length before the copy runs.
        ledger
            .storage_flow
            .is_none()
            .then(|| ledger.exact_array_length(array).or(array.array_len))
            .flatten()
    }

    pub(super) fn array_slice(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        array: &Datum,
        element: &ty::Member,
        (start, end): (Option<usize>, Option<usize>),
        span: Span,
    ) -> Datum {
        let mut slice = Datum::source(span, Access::Mut, true);
        let length = start
            .zip(end)
            .and_then(|(start, end)| end.checked_sub(start));
        if let Some(length) = length {
            ledger.record_array_length(span, length);
        }
        if self.program.is_value(&element.ty) || length == Some(0) {
            return slice;
        }
        let mut project = |ledger: &mut Ledger, coordinate| {
            let mut member =
                self.project_observed(ctx, ledger, array, (coordinate, element.mode.mode, span));
            // The result has a fresh container and still points to the
            // source's elements.
            member.requires_new = false;
            member.transform(&mut |origin| origin.new = false);
            member
        };
        if let (Some(start), Some(1)) = (start, length) {
            slice.members.insert(
                Coordinate::Index("0".into()),
                project(ledger, Coordinate::Index(start.to_string())),
            );
            return slice;
        }
        if let Some(start) = start {
            let source = ledger.snapshot(array);
            for coordinate in source.members.keys() {
                if let Coordinate::Index(index) = coordinate
                    && let Ok(index) = index.parse::<usize>()
                    && index >= start
                    && end.is_none_or(|end| index < end)
                {
                    let member = project(ledger, coordinate.clone());
                    slice
                        .members
                        .insert(Coordinate::Index((index - start).to_string()), member);
                }
            }
        }
        if length != Some(slice.members.len()) {
            let range = start.map_or(Coordinate::Dynamic, Coordinate::ArrayTail);
            slice
                .members
                .insert(Coordinate::Dynamic, project(ledger, range));
        }
        slice
    }

    pub(super) fn constant_map_key(&self, ctx: &Context, id: ExprId) -> Option<Coordinate> {
        let node = self.ast(ctx.file).expr(id);
        let value = if let Expr::Literal(literal) = &node.value {
            ty::literal(literal).ok()?
        } else {
            self.program.static_values.get(&node.span)?.clone()
        };
        matches!(
            value,
            Value::Unit | Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Bytes(_)
        )
        .then(|| Coordinate::Index(ty::render(&value)))
    }

    pub(super) fn member_schema(&self, base: Span, coordinate: &Coordinate) -> (Access, bool) {
        self.schema(self.ty(base), coordinate)
    }

    pub(super) fn schema(&self, ty: &Ty, coordinate: &Coordinate) -> (Access, bool) {
        let (mode, variable) = self.schema_mode(ty, coordinate);
        (Access::from_mode(mode), variable)
    }

    pub(super) fn schema_mode(&self, ty: &Ty, coordinate: &Coordinate) -> (Mode, bool) {
        self.schema_member(ty, coordinate)
            .map_or((Mode::Plain, false), |member| {
                (member.mode.mode, member.mode.variable)
            })
    }

    pub(super) fn schema_member(&self, ty: &Ty, coordinate: &Coordinate) -> Option<ty::Member> {
        let mut cur = std::borrow::Cow::Borrowed(ty);
        let mut active: Vec<std::sync::Arc<crate::ty::Adt>> = Vec::new();
        loop {
            match cur.as_ref() {
                Ty::Draft(inner) => cur = std::borrow::Cow::Owned((**inner).clone()),
                Ty::Adt(adt) if matches!(adt.kind, AdtKind::Nominal | AdtKind::Opaque) => {
                    if active
                        .iter()
                        .rev()
                        .find(|outer| outer.definition == adt.definition)
                        .is_some_and(|outer| !crate::ty::nested_type_argument(outer, adt))
                    {
                        break;
                    }
                    active.push(std::sync::Arc::clone(adt));
                    let Some(layout) = self.program.nominal_layout(adt) else {
                        break;
                    };
                    cur = std::borrow::Cow::Owned(layout);
                }
                _ => break,
            }
        }
        match (cur.as_ref(), coordinate) {
            (Ty::Record(fields, _), Coordinate::Field(name)) => fields.get(name).cloned(),
            (Ty::Tuple(fields), Coordinate::Index(index)) => index
                .parse::<usize>()
                .ok()
                .and_then(|index| fields.get(index).cloned()),
            (Ty::Map(..), Coordinate::MapKey) => None,
            (Ty::Array(member) | Ty::Map(_, member), _) => Some((**member).clone()),
            _ => None,
        }
    }
}
