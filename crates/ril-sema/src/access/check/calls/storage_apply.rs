use super::*;

impl<'program> Analyzer<'program> {
    pub(super) fn source_args<'a>(
        &self,
        fun: &'a ril_syntax::syntax::Function,
        values: &'a [(usize, Mode, Datum)],
        sources: impl Iterator<Item = Span> + 'a,
    ) -> impl Iterator<Item = Datum> + 'a {
        sources.filter_map(move |name| {
            let i = fun
                .signature
                .params
                .iter()
                .position(|param| param.name.as_ref().is_some_and(|n| n.span == name))?;
            values
                .iter()
                .find(|(index, _, _)| *index == i)
                .map(|(_, _, value)| value.clone())
        })
    }

    pub(super) fn inferred_forwarding(
        &self,
        fun: &ril_syntax::syntax::Function,
        values: &[(usize, Mode, Datum)],
        span: Span,
    ) -> Datum {
        // Recursive calls may precede completion of their own return template.
        // Keep every possible formal source and avoid promising fresh new qualification.
        values
            .iter()
            .filter_map(|(index, _, value)| {
                fun.signature
                    .params
                    .get(*index)
                    .filter(|formal| formal.mode == Mode::Via)
                    .map(|_| value.clone())
            })
            .reduce(Datum::joined)
            .map_or_else(
                || self.snapshot_value(span),
                |mut value| {
                    value.requires_new = false;
                    value
                },
            )
    }

    pub(super) fn return_template(
        &mut self,
        fun: &ril_syntax::syntax::Function,
        entry: &CallEntry<'_>,
    ) -> Option<Datum> {
        let (formals, via, returns) = if let Some(definition) = self
            .functions
            .iter()
            .find(|definition| definition.owner == fun.name.span)
        {
            (
                definition.formals.clone(),
                definition.via.clone(),
                definition.returns.clone(),
            )
        } else {
            let provisional = self.recursive_storage.get(&fun.name.span)?.clone();
            (
                provisional.formals,
                provisional.via,
                provisional.result.into_iter().collect(),
            )
        };
        returns
            .iter()
            .map(|datum| self.instantiate_return(&formals, &via, entry, datum, &mut Vec::new()))
            .reduce(Datum::joined)
    }

    pub(super) fn apply_storage_updates(
        &mut self,
        ctx: &Context,
        storage: CallStorage,
        entry: &CallEntry<'_>,
        ledger: &mut Ledger,
        published: bool,
    ) -> bool {
        let CallStorage {
            formals,
            via,
            updates,
            ..
        } = storage;
        let mut applied = true;
        for (index, (region, update)) in updates.into_iter().enumerate() {
            let mut output_path = vec![Coordinate::Index(index.to_string())];
            let Some((member, parent)) = region.selection.split_last() else {
                let mut stored =
                    self.instantiate_return(&formals, &via, entry, &update.value, &mut output_path);
                ledger.remember_return_graph(&stored, entry.span);
                self.check_stored_views(&stored, false, entry.span);
                if ctx.caller_slots.contains(&region.source) {
                    stored.publications.insert(ctx.owner, true);
                }
                stored.transform(&mut |origin| {
                    origin.dependencies.insert(region.source.into());
                });
                let cell = entry
                    .environment
                    .and_then(|env| env.bindings?.cells.get(&region.source));
                // A cell that belongs to this activation is also visible through
                // its lexical binding. Escaping closures keep the cell itself.
                if let Some(cell) =
                    cell.filter(|cell| !Self::current_cell(entry.ledger, region.source, cell))
                {
                    let place = cell.slot_projection(Coordinate::Index("0".into()));
                    applied &= !place.roots.is_empty();
                    if entry.ledger.slots.contains_key(&region.source)
                        && cell
                            .roots
                            .iter()
                            .any(|root| root.region == Region::allocation(region.source))
                    {
                        ledger.replace_slot(region.source, stored.clone(), false);
                    }
                    ledger.replace_member(&place, stored, update.definite);
                } else {
                    applied &= ledger.replace_slot(region.source, stored, update.definite);
                }
                continue;
            };
            let actual = if let Some(formal) = formals
                .iter()
                .position(|formal| *formal == Some(region.source))
            {
                entry
                    .arguments
                    .iter()
                    .zip(entry.spans)
                    .find(|((index, _, _), _)| *index == formal)
                    .map(|((_, _, actual), &span)| (actual, self.ty(span)))
            } else {
                self.capture_binding(entry, region.source)
            };
            let Some((actual, ty)) = actual else {
                applied = false;
                continue;
            };

            let value = self.project_entry_path(entry.ledger, actual, ty, parent);
            let stored =
                self.instantiate_return(&formals, &via, entry, &update.value, &mut output_path);
            let coordinate = if matches!(member, Coordinate::ArrayTail(_)) {
                ledger.append_coordinate(&value, update.definite)
            } else {
                member.clone()
            };
            let place = value.slot_projection(coordinate);
            applied &= self.apply_storage_member(
                ctx,
                ledger,
                &place,
                stored,
                (entry.span, update.definite, published),
            );
        }
        applied
    }

    pub(super) fn apply_storage_member(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        place: &Datum,
        mut stored: Datum,
        (span, definite, published): (Span, bool, bool),
    ) -> bool {
        if published {
            self.record_write(ctx, place);
        }
        ledger.remember_return_graph(&stored, span);
        self.check_stored_views(&stored, false, span);
        stored
            .publications
            .insert(ctx.owner, place.roots.iter().any(|origin| !origin.new));
        ledger.replace_member(place, stored, definite);
        !place.roots.is_empty()
    }

    pub(super) fn closure_storage(
        &mut self,
        ctx: &Context,
        closures: &BTreeMap<Span, ClosureModes>,
        receiver: &Datum,
        entry: &CallEntry<'_>,
        defer: bool,
    ) -> Option<Ledger> {
        if !ctx.runtime
            || ctx.shadow
            || !ctx.reachable
            || (!defer
                && closures
                    .values()
                    .all(|closure| closure.updates.is_empty() && closure.storage_flow.is_none())
                && receiver.roots.iter().all(|root| {
                    snapshot_invocations::known_provider(root)
                        .is_none_or(|owner| !self.has_imported_provider_storage(owner))
                }))
        {
            return None;
        }
        let alternatives: Vec<_> = receiver
            .roots
            .iter()
            .map(|root| {
                let mut after = entry.ledger.clone();
                let Some((owner, closure)) = Self::known_closure(closures, root) else {
                    if let Some(owner) = snapshot_invocations::known_provider(root)
                        && self.has_imported_provider_storage(owner)
                    {
                        self.replay_provider_storage(
                            ctx,
                            (owner, root, receiver),
                            entry,
                            &mut after,
                        );
                    } else if defer {
                        self.defer_storage_invocation(ctx, &mut after, receiver, root, entry);
                    }
                    return after;
                };
                let captures = Self::closure_captures(entry.ledger, receiver, root, closure);
                let storage = CallStorage {
                    formals: closure.formals.clone(),
                    via: closure.via.clone(),
                    updates: closure.updates.clone(),
                    flow: closure.storage_flow.clone(),
                    ..CallStorage::default()
                };
                let entry = CallEntry {
                    environment: Some(CallEnvironment {
                        owner,
                        bindings: Some(&captures),
                    }),
                    ..*entry
                };
                self.apply_callable_storage(ctx, storage, &entry, &mut after, false);
                after
            })
            .collect();
        let mut after = entry.ledger.clone();
        after.merge(entry.ledger, &alternatives);
        Some(after)
    }

    pub(super) fn defer_storage_invocation(
        &self,
        ctx: &Context,
        ledger: &mut Ledger,
        receiver: &Datum,
        root: &Origin,
        entry: &CallEntry<'_>,
    ) {
        if !(ctx.formals.contains(&Some(root.region.source))
            || receiver
                .capture_paths
                .keys()
                .any(|path| path.owner == ctx.owner)
            || root.callback_result.is_some()
            || root.storage_read.is_some())
        {
            return;
        }
        let mut receiver = receiver.clone();
        receiver.retain_compatible_origins(&root.branches);
        receiver.roots.retain(|origin| origin == root);
        ledger.defer_storage_call(DeferredStorageCall {
            site: entry
                .invocation
                .last()
                .map_or(entry.span, |invocation| invocation.span),
            receiver,
            arguments: entry.arguments.to_vec(),
            spans: entry.spans.to_vec(),
        });
    }

    pub(super) fn known_closures(&self, receiver: &Datum) -> BTreeMap<Span, ClosureModes> {
        receiver
            .roots
            .iter()
            .filter_map(|root| {
                let owner = snapshot_invocations::known_provider(root)?;
                self.closure_modes
                    .get(&owner)
                    .map(|modes| (owner, modes.clone()))
            })
            .collect()
    }

    pub(super) fn known_closure<'m>(
        closures: &'m BTreeMap<Span, ClosureModes>,
        root: &Origin,
    ) -> Option<(Span, &'m ClosureModes)> {
        let owner = snapshot_invocations::known_provider(root)?;
        Some((owner, closures.get(&owner)?))
    }

    pub(super) fn closure_captures(
        ledger: &Ledger,
        receiver: &Datum,
        root: &Origin,
        closure: &ClosureModes,
    ) -> CapturedBindings {
        let mut environment = receiver.clone();
        environment.retain_compatible_origins(&root.branches);
        let mut bindings = CapturedBindings::default();
        for (index, &(binding, variable)) in closure.captures.iter().enumerate() {
            let Some(mut captured) =
                environment.known_member(&Coordinate::Index(index.to_string()))
            else {
                continue;
            };
            let current_cell = variable && Self::current_cell(ledger, binding, &captured);
            if variable {
                let value = ledger.project(&captured, Coordinate::Index("0".into()), Access::Mut);
                bindings.cells.insert(binding, captured);
                captured = value;
            }
            if let Some(slot) = ledger.slots.get(&binding) {
                let mut current = slot.value.clone();
                current.retain_compatible_origins(&root.branches);
                if current_cell
                    || (!variable
                        && !captured.roots.is_empty()
                        && captured.roots.iter().all(|origin| {
                            current
                                .roots
                                .iter()
                                .any(|current| current.region == origin.region)
                        }))
                {
                    captured = current;
                }
            }
            bindings.values.insert(binding, captured);
        }
        bindings
    }

    pub(super) fn current_cell(ledger: &Ledger, binding: Span, cell: &Datum) -> bool {
        ledger.slots.contains_key(&binding)
            && !cell.roots.is_empty()
            && cell
                .roots
                .iter()
                .all(|root| root.region == Region::allocation(binding))
    }

    pub(super) fn capture_binding<'e>(
        &self,
        entry: &CallEntry<'e>,
        binding: Span,
    ) -> Option<(&'e Datum, &'program Ty)> {
        let environment = entry.environment?;
        let value = match environment.bindings {
            Some(bindings) => bindings.values.get(&binding),
            None => entry.ledger.slots.get(&binding).map(|slot| &slot.value),
        }?;
        let ty = self
            .definition(binding)
            .and_then(|id| self.program.bindings.get(&id))
            .unwrap_or(&Ty::Unknown);
        Some((value, ty))
    }

    pub(super) fn project_entry_path(
        &self,
        ledger: &Ledger,
        base: &Datum,
        ty: &Ty,
        path: &[Coordinate],
    ) -> Datum {
        let mut value = base.clone();
        let mut ty = ty.clone();
        for coordinate in path {
            let schema = self.schema_member(&ty, coordinate);
            let mode = schema.as_ref().map_or_else(
                || {
                    if ty == Ty::Unknown {
                        Mode::Mut
                    } else {
                        Mode::Plain
                    }
                },
                |member| member.mode.mode,
            );
            value = ledger.project_schema(&value, coordinate.clone(), mode);
            ty = schema.map_or(Ty::Unknown, |member| member.ty);
        }
        value
    }
}
